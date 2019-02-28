package edu.kit.iti.formal.automation.plcopenxml

import edu.kit.iti.formal.util.CodeWriter
import org.jdom2.Element
import org.jdom2.filter.Filters
import org.jdom2.xpath.XPathFactory


private val xpathFactory = XPathFactory.instance()


internal fun getVariables(block: Element, child: String) =
        block.getChild(child)?.children?.map { BlockVariable(it) } ?: listOf()

internal fun operatorSymbol(name: String) =
        when (name.toLowerCase()) {
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
class FBDTranslator(val e: Element, val writer: CodeWriter) {
    val nodes: List<FbdNode>

    init {
        val nodes = e.getChild("body").getChild("FBD").children.mapNotNull { translateBlock(it) }
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

enum class FBDCallType { UNKNOWN, FUNCTION, OPERATOR, EXECUTE }

sealed class FbdNode(val block: Element, val network: FBDTranslator) {
    val id: String by lazy { block.getAttributeValue("localId") }
    val networkId by lazy {
        //This is a codesys assumption!
        if (id[1] != '0') throw IllegalStateException("I am not tested for more than 9 FBD networks!")
        id[0].toInt() - 49
    }
    var executionOrder = 0

    val outputVariables by lazy { getVariables(block, "outputVariables") }
    val inoutVariables by lazy { getVariables(block, "inoutVariables") }
    val inputVariables by lazy {
        getVariables(block, "inputVariables")
    }

    open val predessorIds by lazy {
        (inputVariables + inoutVariables).mapNotNull { it.connectionInId }
    }

    var predessorBlocks = listOf<FbdNode>()

    abstract fun write(writer: CodeWriter)
    abstract fun getSlot(formalParameterName: String?): String?
}


class FbdBlock(e: Element, network: FBDTranslator) : FbdNode(e, network) {
    val type: String by lazy { block.getAttributeValue("typeName") }
    val instanceName: String by lazy {
        block.getAttributeValue("instanceName") ?: this.type.toLowerCase()
    }


    val callType: FBDCallType by lazy {
        when (type.toLowerCase()) {
            "mux" -> FBDCallType.FUNCTION
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

    /*
    val assignTo: String? by lazy {
        if (callType == FBDCallType.OPERATOR ||
                callType == FBDCallType.FUNCTION) "op${id}"
        else null
    }
    */


    val executeBody: String? by lazy {
        val key = "http://www.3s-software.com/plcopenxml/stcode"
        //val query = xpathFactory.compile(".//data[@name=\"$key\"]/STCode/text()", Filters.textOnly())
        val query = xpathFactory.compile(".//STCode", Filters.element())
        val a = query.evaluateFirst(block)
        a?.textTrim
    }

    override fun getSlot(formalParameterName: String?): String? {
        val neg = outputVariables.find { it.formalParameter == formalParameterName }?.negated ?: false
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
        }
    }

    private fun getExpression() = when (callType) {
        FBDCallType.OPERATOR -> {
            val opSymbol = operatorSymbol(instanceName)
            val terms = inputVariables
                    .sortedWith(compareBy(BlockVariable::formalParameter))
                    .joinToString(opSymbol, "(", ")") { network.getSlot(it) }
            terms
        }
        FBDCallType.FUNCTION -> "$instanceName(${getArguments()})"
        else -> ""
    }

    private fun getArguments() = inputVariables
            .sortedWith(compareBy(BlockVariable::formalParameter))
            .joinToString(", ") {
                val e = network.getSlot(it)
                if (callType == FBDCallType.FUNCTION) e
                else "${it.formalParameter} := $e"
            }

    override fun write(writer: CodeWriter) {
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
    }
}

class FbdJump(e: Element, network: FBDTranslator) : FbdNode(e, network) {
    val variable = BlockVariable(e)
    val target by lazy { e.getAttributeValue("label") }

    override val predessorIds by lazy {
        val v = variable.connectionInId
        if (v != null) listOf(v) else listOf()
    }


    override fun write(writer: CodeWriter) {
        val cond = network.getSlot(variable)
        writer.nl().cblock("IF $cond THEN", "END_IF") { write("JUMP $target;") }
    }

    override fun getSlot(formalParameterName: String?): String? {
        return "/*JUMP does not have any slots!*/"
    }
}

class FbdReturn(e: Element, network: FBDTranslator) : FbdNode(e, network) {
    val variable = BlockVariable(e)

    override fun write(writer: CodeWriter) {
        val cond = network.getSlot(variable)
        writer.nl().cblock("IF $cond THEN", "END_IF") { write("RETURN;") }
    }

    override fun getSlot(formalParameterName: String?): String? {
        return "/*RETURN does not have any slots!*/"
    }
}

class FbdLabel(e: Element, network: FBDTranslator) : FbdNode(e, network) {
    val label by lazy { e.getAttributeValue("label") }

    override fun write(writer: CodeWriter) {
        writer.nl().write("$label:").nl()
    }

    override fun getSlot(formalParameterName: String?): String? {
        return "/*RETURN does not have any slots!*/"
    }
}

class InVariable(e: Element, network: FBDTranslator) : FbdNode(e, network) {
    override fun write(writer: CodeWriter) {}

    val expression: String? by lazy {
        block.getChildText("expression")
    }

    override fun getSlot(formalParameterName: String?): String? {
        return expression
    }
}

class OutVariable(e: Element, network: FBDTranslator) : FbdNode(e, network) {
    val expression: String? by lazy {
        block.getChildText("expression")
    }
    val variable = BlockVariable(e)


    override val predessorIds by lazy {
        val v = variable.connectionInId
        if (v != null) listOf(v) else listOf()
    }


    override fun getSlot(formalParameterName: String?): String? = "/*no slot for out variables*/"

    override fun write(writer: CodeWriter) {
        val value = network.getSlot(variable)
        writer.write(expression!!).write(" := ").write(value).write(";")
    }
}

class InOutVariable(e: Element, network: FBDTranslator) : FbdNode(e, network) {
    val expression: String by lazy {
        block.getChildText("expression") ?: throw IllegalStateException()
    }

    /*override val predessorIds by lazy {
        val v = variable.connectionInId
        if (v != null) listOf(v) else listOf()
    }*/

    override fun getSlot(formalParameterName: String?): String? = expression

    override fun write(writer: CodeWriter) {
        val value = network.getSlot(inputVariables.first())
        writer.nl().write(expression).write(" := ").write(value)
    }
}

class BlockVariable(val element: Element) {
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
        "TRUE" == element.getAttributeValue("negated")
    }

    val stored: Boolean = false

    val reset: Boolean = false
}
