package edu.kit.iti.formal.automation.plcopenxml

import edu.kit.iti.formal.automation.fbd.*
import edu.kit.iti.formal.automation.fbd.FbdNode.*
import edu.kit.iti.formal.automation.fbd.FbdNode.Function
import edu.kit.iti.formal.util.CodeWriter
import org.jdom2.Element
import org.jdom2.filter.Filters
import org.jdom2.xpath.XPathFactory
import java.util.*

private val xpathFactory = XPathFactory.instance()


internal fun getVariables(block: Element, child: String) =
    block.getChild(child)?.children?.map { BlockVariable(it) } ?: listOf()

internal fun operatorSymbol(name: String) =
    when (name.lowercase(Locale.getDefault())) {
        "eq" -> " = "
        "sub" -> " - "
        "add" -> " + "
        "div" -> " / "
        "mult" -> " * "
        "and" -> " AND "
        "or" -> " OR "
        "xor" -> " ^ "
        else -> "/*!! UNKNOWN OP: $name !!*/"
    }

//TODO: Edges could be negated
//TODO: Storage modifier (S=, R=)
//TODO: Edge modifier
//TODO: Jumps and Marks
/*
class FBDTranslator(val fbd: Element, val writer: CodeWriter) {
    val nodes: List<FbdNode>

    init {
        val nodes = fbd.children.mapNotNull { translateBlock(it) }
        nodes.forEach { n ->
            n.predessorBlocks = n.predessorIds.mapNotNull { ref -> nodes.find { it.id == ref } }
        }
        var fixpt: Boolean
        do {
            fixpt = true
            for (node in nodes) {
                val predOrder =
                        (node.predessorBlocks.asSequence().map { it.executionOrder }.max() ?: -1) + 1
                if (node.executionOrder != predOrder) {
                    fixpt = false
                    node.executionOrder = predOrder
                }
            }
        } while (!fixpt)
        this.nodes = nodes.sortedBy { it.executionOrder }
    }

    fun run() {
        writer.nl().printf("VAR").block {
            nodes.mapNotNull { it as? FbdBlock }
                    .filter { it.callType == FBDCallType.UNKNOWN }
                    .forEach {
                        nl().printf("${it.instanceName} : ${it.type};")
                    }
        }
        writer.nl().printf("END_VAR").nl()

        val networks = nodes.groupBy { it.networkId }
        val networkIds = networks.keys.sorted()

        for (nId in networkIds) {
            val nodes = networks[nId]!!.sortedBy { it.executionOrder }
            writer.nl().write("// Start of a new network: $nId").nl()
            nodes.forEach {
                writer.nl().write("// id: ${it.id}, execOrder: ${it.executionOrder}").nl()
                it.write(writer)
            }
        }
        writer.nl()
    }

    private fun translateBlock(block: Element) = when (block.name) {
        "block" -> FbdBlock(block, this)
        "inVariable" -> InVariable(block, this)
        "outVariable" -> OutVariable(block, this)
        "jump" -> FbdJump(block, this)
        "return" -> FbdReturn(block, this)
        "label" -> FbdLabel(block, this)
        "vendorElement" -> {
            println("Vendor Elements not supported in FBDs.")
            null
        }
        else -> throw IllegalStateException()
    }

    internal fun findNode(id: String?) = nodes.find { it.id == id }

    internal fun getSlot(variable: BlockVariable): String {
        val v = findNode(variable.connectionInId)?.getSlot(variable.connectionInParam) ?: "/*notfound*/"
        return if (variable.negated) "NOT $v" else v
    }

}
*/

class FBDTranslator(val fbd: Element, val writer: CodeWriter) {
    val nodes: List<FbdNode>

    init {
        nodes = fbd.children.mapNotNull { translateBlock(it) }
        nodes.forEach { n ->
            n.predessorBlocks = n.predessorIds.mapNotNull { ref -> nodes.find { it.id == ref } }
        }
    }

    fun generateFbdBody(): FbdBody {
        val body = FbdBody()
        val networks = nodes.groupBy { it.networkId }
        val networkIds = networks.keys.sorted()
        for (nId in networkIds) {
            val nodes = networks[nId] ?: error("Never happen")
            val diagram = FbDiagram().also { body += it }
            nodes.forEach {
                it.write(diagram)
            }
        }
        return body
    }

    fun run() {
        val fbdBody = generateFbdBody()
        val body = fbdBody.toJson()
        writer.nl().write("(***FBD\n$body\n***)")
    }

    private fun translateBlock(block: Element) = when (block.name) {
        "block" -> FbdBlock(block, this)
        "inVariable" -> InVariable(block, this)
        "outVariable" -> OutVariable(block, this)
        "inOutVariable" -> InOutVariable(block, this)
        "jump" -> FbdJump(block, this)
        "return" -> FbdReturn(block, this)
        "label" -> FbdLabel(block, this)
        "vendorElement" -> {
            println("Vendor Elements not supported in FBDs.")
            null
        }

        else -> throw IllegalStateException("Xml element: ${block.name}")
    }

    internal fun findNode(id: String?) = nodes.find { it.id == id }

    /*internal fun getSlot(variable: BlockVariable): String {
        val v = findNode(variable.connectionInId)?.getSlot(variable.connectionInParam) ?: "/*notfound*/"
        return if (variable.negated) "NOT $v" else v
    }*/
}

enum class FBDCallType { UNKNOWN, FUNCTION, OPERATOR, EXECUTE }

sealed class FbdNode(val block: Element, val network: FBDTranslator) {
    val id: String by lazy { block.getAttributeValue("localId") }
    val networkId by lazy {
        if (id.length > 5) {
            //This is a codesys assumption!
            if (id[1] != '0') throw IllegalStateException("I am not tested for more than 9 FBD networks!")
            id[0].toInt() - 49
        } else 0
    }

    val outputVariables by lazy { getVariables(block, "outputVariables") }
    val inoutVariables by lazy { getVariables(block, "inoutVariables") }
    open val inputVariables by lazy {
        getVariables(block, "inputVariables")
    }

    open val predessorIds by lazy {
        (inputVariables + inoutVariables).mapNotNull { it.connectionInId }
    }

    var predessorBlocks = listOf<FbdNode>()

    abstract val fbdNode: edu.kit.iti.formal.automation.fbd.FbdNode

    open fun write(dia: FbDiagram) {
        val n = fbdNode
        dia += n
        inputVariables.forEach { n.inputSlots.add(it.asInput) }
        outputVariables.forEach { n.outputSlots.add(it.asOutput) }
        inoutVariables.forEach { n.inOutSlots.add(it.formalParameter) }

        inputVariables.forEach { v ->
            val out = predessorBlocks.find { it.id == v.connectionInId }?.getSlot(v.formalParameter)
            if (out != null) {
                dia.edges.add(FbdEdge(out.gid, v.asInput.gid))
            }
        }

    }

    open fun getSlot(formalParameterName: String?): FbdOutput? = null
}

class FbdBlock(e: Element, network: FBDTranslator) : FbdNode(e, network) {
    val type: String by lazy { block.getAttributeValue("typeName") }
    val instanceName: String by lazy {
        block.getAttributeValue("instanceName") ?: this.type.lowercase(Locale.getDefault())
    }

    val callType: FBDCallType by lazy {
        when (type.lowercase(Locale.getDefault())) {
            "mux" -> FBDCallType.FUNCTION
            "add" -> FBDCallType.OPERATOR
            else -> {
                val ct = xpathFactory.compile(".//CallType", Filters.element()).evaluateFirst(block)
                when (ct?.textTrim) {
                    "function" -> FBDCallType.FUNCTION
                    "operator" -> FBDCallType.OPERATOR
                    "execute" -> FBDCallType.EXECUTE
                    else -> FBDCallType.UNKNOWN
                }
            }
        }
    }

    val executeBody: String? by lazy {
        val key = "http://www.3s-software.com/plcopenxml/stcode"
        //val query = xpathFactory.compile(".//data[@name=\"$key\"]/STCode/text()", Filters.textOnly())
        val query = xpathFactory.compile(".//STCode", Filters.element())
        val a = query.evaluateFirst(block)
        a?.textTrim
    }

    override fun getSlot(formalParameterName: String?): FbdOutput? {
        if (outputVariables.size == 1)
            return outputVariables.first().asOutput

        return outputVariables.find { it.formalParameter.equals(formalParameterName, true) }?.asOutput

        /*val neg = variable?.negated ?: false
        val prefix = (if (neg) "NOT " else "")
        return when (callType) {
            FBDCallType.EXECUTE -> {
                prefix + network.getSlot(inputVariables.first()) // same as input
            }
            FBDCallType.UNKNOWN -> {
                "$prefix$instanceName.$formalParameterName"
            }
            else ->
                "$prefix(${getExpression()})"
        }*/
    }

    /*private fun getExpression() = when (callType) {
        FBDCallType.OPERATOR -> {
            val opSymbol = operatorSymbol(instanceName)
            val terms = inputVariables
                    //.sortedWith(compareBy(BlockVariable::formalParameter))
                    .joinToString(opSymbol, "(", ")") { network.getSlot(it) }
            terms
        }
        FBDCallType.FUNCTION -> "$type(${getArguments()})"
        else -> ""
    }*/

    /*private fun getArguments() = inputVariables
            //.sortedWith(compareBy(BlockVariable::formalParameter))
            .joinToString(", ") {
                val e = network.getSlot(it)
                if (callType == FBDCallType.FUNCTION) e
                else "${it.formalParameter} := $e"
            }
    */

    override val fbdNode by lazy {
        when (callType) {
            FBDCallType.EXECUTE -> {
                Execute(executeBody ?: "//NO BODY WAS FOUND!")
            }

            FBDCallType.OPERATOR -> Operator(instanceName)
            FBDCallType.FUNCTION -> Function(instanceName)
            FBDCallType.UNKNOWN -> FunctionBlock(instanceName)
        }
    }
}

class FbdJump(e: Element, network: FBDTranslator) : FbdNode(e, network) {
    val variable = BlockVariable(e)
    val target by lazy { e.getAttributeValue("label") }
    val blockVariable = BlockVariable(e)
    override val inputVariables: List<BlockVariable>
        get() = listOf(blockVariable)

    override val predessorIds by lazy {
        val v = variable.connectionInId
        if (v != null) listOf(v) else listOf()
    }

    override val fbdNode by lazy { Jump(target) }
}

class FbdReturn(e: Element, network: FBDTranslator) : FbdNode(e, network) {
    val variable = BlockVariable(e)
    override val inputVariables: List<BlockVariable>
        get() = listOf(variable)

    override val fbdNode by lazy { Return }
}

class FbdLabel(e: Element, network: FBDTranslator) : FbdNode(e, network) {
    val label by lazy { e.getAttributeValue("label") }
    override val fbdNode by lazy { Jump(label) /* nobody cares for this value */ }
    override fun write(dia: FbDiagram) {
        dia.label = label
    }
}

class InVariable(e: Element, network: FBDTranslator) : FbdNode(e, network) {
    override val fbdNode by lazy {
        Variable(expression, read = true).also {
            it.outputSlots.add(FbdOutput(expression = expression))
        }
    }

    val expression: String? by lazy {
        block.getChildText("expression")
    }

    override fun getSlot(formalParameterName: String?): FbdOutput = fbdNode.outputSlots.first()
}

class OutVariable(e: Element, network: FBDTranslator) : FbdNode(e, network) {
    val expression: String? by lazy {
        block.getChildText("expression")
    }
    val variable = BlockVariable(e)
    override val inputVariables: List<BlockVariable>
        get() = listOf(variable)

    override val fbdNode by lazy { Variable(expression, store = true) }
    //.also { it.inputSlots.add(variable.asInput) } }

    override val predessorIds by lazy {
        val v = variable.connectionInId
        if (v != null) listOf(v) else listOf()
    }

    override fun write(dia: FbDiagram) {
        super.write(dia)
    }
}

class InOutVariable(e: Element, network: FBDTranslator) : FbdNode(e, network) {
    val expression: String by lazy {
        block.getChildText("expression") ?: throw IllegalStateException()
    }

    override fun getSlot(formalParameterName: String?) = FbdOutput(expression = expression)

    override val fbdNode by lazy { Variable(expression, true, true) }
}

class BlockVariable(val element: Element) {
    val asInput by lazy { FbdInput(formalParameter ?: "", negated, stored, reset) }
    val asOutput by lazy { FbdOutput(formalParameter ?: "", expression) }

    val expression: String? by lazy {
        element.getChildText("expression")
    }
    val formalParameter by lazy {
        element.getAttributeValue("formalParameter")
    }
    val connectionInId by lazy {
        element.getChild("connectionPointIn")?.getChild("connection")?.getAttributeValue("refLocalId")
    }
    val connectionInParam by lazy {
        element.getChild("connectionPointIn")?.getChild("connection")?.getAttributeValue("formalParameter")
    }

    val negated: Boolean by lazy {
        "true" == element.getAttributeValue("negated")
    }

    val stored: Boolean = false

    val reset: Boolean = false
}
