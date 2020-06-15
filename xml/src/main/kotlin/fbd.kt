package edu.kit.iti.formal.automation.fbd

import com.fasterxml.jackson.annotation.JsonIgnore
import com.fasterxml.jackson.annotation.JsonSubTypes
import com.fasterxml.jackson.annotation.JsonSubTypes.Type
import com.fasterxml.jackson.annotation.JsonTypeInfo
import com.fasterxml.jackson.databind.DeserializationFeature
import com.fasterxml.jackson.databind.ObjectMapper
import com.fasterxml.jackson.databind.SerializationFeature
import edu.kit.iti.formal.automation.plcopenxml.operatorSymbol
import edu.kit.iti.formal.util.CodeWriter
import edu.kit.iti.formal.util.HasMetadata
import edu.kit.iti.formal.util.HasMetadataImpl
import edu.kit.iti.formal.util.Metadata
import java.util.concurrent.atomic.AtomicInteger

/**
 * Support for function block diagrams.
 *
 * @author Alexander Weigl
 * @version 1 (10.07.19)
 */
class FbdBody(val diagrams: ArrayList<FbDiagram> = ArrayList<FbDiagram>())
    : MutableList<FbDiagram> by diagrams, HasMetadata by HasMetadataImpl() {
    fun toJson(): String {
        return om.writeValueAsString(this)
    }

    fun writeDot(out: CodeWriter) {
        out.cblock("digraph G {", "}") {
            out.println("rankdir=\"LR\";")
            diagrams.forEach { it.writeDot(out) }
        }
    }

    fun asStructuredText(out: CodeWriter) {
        diagrams.forEach { it.asStructuredText(out) }
    }

    companion object {
        val om = ObjectMapper().also {
            it.configure(DeserializationFeature.USE_BIG_INTEGER_FOR_INTS, true)
            it.enable(SerializationFeature.INDENT_OUTPUT)
            //it.enableDefaultTyping(ObjectMapper.DefaultTyping.OBJECT_AND_NON_CONCRETE, JsonTypeInfo.As.PROPERTY)
        }

        fun fromJson(s: String) = om.readValue<FbdBody>(s, FbdBody::class.java)
    }
}


data class FbDiagram(
        var label: String? = null,
        var nodes: MutableList<FbdNode> = ArrayList(),
        var edges: MutableList<FbdEdge> = ArrayList()) : HasMetadata by HasMetadataImpl() {

    fun topsorted(): List<FbdNode> {
        updateExecutionOrder()
        return nodes.sortedBy { it.executionOrder }
    }

    fun asStructuredText(out: CodeWriter) {
        out.print("$label:").block {
            topsorted().forEach { n ->
                n.asStructuredText(this@FbDiagram, out)
            }
        }
    }

    fun updateExecutionOrder() {
        nodes.forEach { it.executionOrder = 0 }
        val pred = nodes.map {
            it to it.inputSlots.mapNotNull { findOutputForInput(it)?.first }
        }.toMap()

        var fixpt: Boolean
        do {
            fixpt = true
            for (node in nodes) {
                val predOrder = (pred[node]?.map { it.executionOrder }?.max() ?: 0) + 1
                if (node.executionOrder != predOrder) {
                    fixpt = false
                    node.executionOrder = predOrder
                }
            }
        } while (!fixpt)
    }


    fun findSlot(gid: String): Pair<FbdNode, FbdSlot>? {
        val byId = { s: FbdSlot -> gid == s.gid }
        nodes.forEach {
            val s = it.inputSlots.find(byId) ?: it.outputSlots.find(byId)
            if (s != null) return it to s
        }
        return null
    }

    fun connections() = edges.map { (a, b) -> findSlot(a) to findSlot(b) }

    operator fun plusAssign(node: FbdNode) {
        nodes.add(node)
    }

    fun writeDot(out: CodeWriter) {
        out.cblock("subgraph cluster_$label {", "}") {
            nl().println("label = \"$label\";")
            nl().println("graph[color=blue];")

            nodes.forEach {
                val i = it.inputSlots.joinToString("|") { "<${it.gid}> ${it.formalName}" }
                val o = it.outputSlots.joinToString("|") { "<${it.gid}> ${it.formalName}" }
                when (it) {
                    is FbdNode.Jump -> {
                        out.println("${it.id} [shape=Msquare,label=\"${it.target}\"];")
                    }
                    FbdNode.Return -> out.write("${it.id} [shape=Msquare,label=\"return\"];")
                    is FbdNode.Operator ->
                        out.println("${it.id} [shape=record,label=\" ${it.op} | { {$i} | {$o} }\"];")
                    is FbdNode.Function ->
                        out.println("${it.id} [shape=record,label=\"${it.functionName} | { {$i} | {$o} }\"];")
                    is FbdNode.FunctionBlock ->
                        out.println("${it.id} [shape=record,label=\"${it.instanceName} | { {$i} | {$o} }\"];")
                    is FbdNode.Execute ->
                        out.println("${it.id} [shape=record,label=\"execute | { {$i} | {$o} }\"];")
                    is FbdNode.Variable -> {
                        out.println("${it.id} [shape=rect,label=${it.ref}];")
                    }
                }
            }

            connections().forEach { (a, b) ->
                if (a != null && b != null) {
                    val (nodeFrom, slotFrom) = a
                    val (nodeTo, slotTo) = b
                    val from = if (nodeFrom is FbdNode.Variable) nodeFrom.id else "${nodeFrom.id}:${slotFrom.gid}"
                    val to = if (nodeTo is FbdNode.Variable) nodeTo.id else "${nodeTo.id}:${slotTo.gid}"
                    out.println("$from -> $to; ")
                } else {
                    throw IllegalStateException("$a $b")
                }
            }
        }
    }

    fun findOutputForInput(input: FbdInput): Pair<FbdNode, FbdSlot>? {
        return edges.find { (a, b) -> b == input.gid }
                ?.let { findSlot(it.from) }
    }
}

data class FbdEdge(val from: String, val to: String)
    : HasMetadata by HasMetadataImpl()

interface FbdSlot : HasMetadata {
    val gid: String
    var formalName: String
}

data class FbdInput(override var formalName: String = "",
                    var negated: Boolean = false,
                    var store: Boolean = false,
                    var reset: Boolean = false) : FbdSlot, HasMetadata by HasMetadataImpl() {
    override var gid: String = counter.incrementAndGet().toString()
}

class FbdOutput(override var formalName: String = "", var expression: String?)
    : FbdSlot, HasMetadata by HasMetadataImpl() {
    override var gid: String = counter.incrementAndGet().toString()
}

private val counter = AtomicInteger()

@JsonTypeInfo(
        use = JsonTypeInfo.Id.NAME,
        include = JsonTypeInfo.As.PROPERTY,
        property = "type")
@JsonSubTypes(
        Type(FbdNode.Jump::class, name = "jmp"),
        Type(FbdNode.Return::class, name = "ret"),
        Type(FbdNode.Operator::class, name = "op"),
        Type(FbdNode.FunctionBlock::class, name = "fbd"),
        Type(FbdNode.Function::class, name = "func"),
        Type(FbdNode.Execute::class, name = "exec"),
        Type(FbdNode.Variable::class, name = "var")
)
sealed class FbdNode : HasMetadata by HasMetadataImpl() {
    val id: String = counter.getAndIncrement().toString()

    var inputSlots = arrayListOf<FbdInput>()
    var inOutSlots = arrayListOf<String>()
    var outputSlots = arrayListOf<FbdOutput>()

    @JsonIgnore
    var executionOrder: Int = 0

    open fun asStructuredText(fbDiagram: FbDiagram, out: CodeWriter) {}
    open fun getOutputValue(fbd: FbDiagram, slot: FbdSlot): String = "/* no supported slot */"

    //data class Label(val name: String) : FbdNode()

    data class Jump(val target: String) : FbdNode() {
        override fun asStructuredText(fbDiagram: FbDiagram, out: CodeWriter) {
            fbDiagram.findOutputForInput(inputSlots.first())?.let { (n, slot) ->
                val cond = n.getOutputValue(fbDiagram, slot)
                out.nl().cblock("IF $cond THEN", "END_IF") { write("JUMP $target;") }
            }
        }
    }

    object Return : FbdNode() {
        override fun asStructuredText(fbDiagram: FbDiagram, out: CodeWriter) {
            fbDiagram.findOutputForInput(inputSlots.first())?.let { (n, slot) ->
                val cond = n.getOutputValue(fbDiagram, slot)
                out.nl().cblock("IF $cond THEN", "END_IF") { write("RETURN;") }
            }
        }
    }

    data class Operator(val op: String) : FbdNode() {
        override fun asStructuredText(fbDiagram: FbDiagram, out: CodeWriter) {}

        override fun getOutputValue(fbd: FbDiagram, slot: FbdSlot): String {
            val symbol = operatorSymbol(op)
            val terms = inputSlots
                    .mapNotNull { fbd.findOutputForInput(it) }
                    .joinToString(symbol, "(", ")") { (n, s) ->
                        n.getOutputValue(fbd, s)
                    }
            return terms
        }
    }

    data class Function(val functionName: String) : FbdNode() {
        override fun asStructuredText(fbDiagram: FbDiagram, out: CodeWriter) {

        }

        override fun getOutputValue(fbd: FbDiagram, slot: FbdSlot): String {
            val terms = inputSlots
                    .mapNotNull { fbd.findOutputForInput(it) }
                    .joinToString(", ", "$functionName(", ")") { (n, s) ->
                        n.getOutputValue(fbd, s)
                    }
            return terms
        }
    }

    data class FunctionBlock(val instanceName: String) : FbdNode() {
        override fun asStructuredText(fbDiagram: FbDiagram, out: CodeWriter) {
            val args = inputSlots.mapNotNull { fbDiagram.findOutputForInput(it) }
                    .joinToString(", ") { (n, s) -> n.getOutputValue(fbDiagram, s) }
            out.nl().write("$instanceName($args);")
        }

        override fun getOutputValue(fbd: FbDiagram, slot: FbdSlot): String {
            return "$instanceName.${slot.formalName}"
        }
    }

    data class Execute(var body: String) : FbdNode() {
        override fun asStructuredText(fbDiagram: FbDiagram, out: CodeWriter) {
            super.asStructuredText(fbDiagram, out)
            fbDiagram.findOutputForInput(inputSlots.first())?.also { (n, slot) ->
                val cond = n.getOutputValue(fbDiagram, slot)
                out.nl().cblock("IF $cond THEN", "END_IF") { appendReformat(body) }
            }
        }

        override fun getOutputValue(fbd: FbDiagram, slot: FbdSlot): String {
            return fbd.findOutputForInput(inputSlots.first())?.let { (n, s) ->
                n.getOutputValue(fbd, s)
            } ?: "/*error?*/"
        }
    }

    data class Variable(val ref: String?,
                        val store: Boolean = false,
                        val read: Boolean = false) : FbdNode() {
        override fun asStructuredText(fbDiagram: FbDiagram, out: CodeWriter) {
            if (store) {
                fbDiagram.findOutputForInput(inputSlots.first())?.let { (n, s) ->
                    out.nl().write("$ref := ${n.getOutputValue(fbDiagram, s)};")
                }
            }
        }

        override fun getOutputValue(fbd: FbDiagram, slot: FbdSlot): String {
            return ref!!
        }
        /*    val value = network.getSlot(variable)
        val not = if (variable.negated) "NOT " else ""
        writer.write("$expression := $not $value;");
    */
    }
}

/*
writer.nl().printf("VAR").block {
            nodes.mapNotNull { it as? FbdBlock }
                    .filter { it.callType == FBDCallType.UNKNOWN }
                    .forEach {
                        nl().printf("${it.instanceName} : ${it.type};")
                    }
        }
        writer.nl().printf("END_VAR").nl()

            when (callType) {
                FBDCallType.EXECUTE -> {
                    val cond = network.getSlot(inputVariables.first())
                    writer.nl().cblock("IF $cond THEN", "END_IF") {
                        writer.appendReformat(executeBody ?: "//NO BODY WAS FOUND!")
                    }
                }
                FBDCallType.OPERATOR -> writer.write("//Operator: ${getExpression()}")
                FBDCallType.FUNCTION -> writer.write("//Function: ${getExpression()}")
                FBDCallType.UNKNOWN -> writer.write("$instanceName(${getArguments()});")
            }
 */