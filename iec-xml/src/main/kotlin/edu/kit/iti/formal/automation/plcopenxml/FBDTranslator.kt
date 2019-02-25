package edu.kit.iti.formal.automation.plcopenxml

import edu.kit.iti.formal.util.CodeWriter
import org.jdom2.Element
import org.jdom2.filter.Filters
import org.jdom2.xpath.XPathFactory

//TODO: Edges could be negated
//TODO: Storage modifier (S=, R=)
//TODO: Edge modifier
class FBDTranslator(val e: Element, val writer: CodeWriter) {
    val blockVariables = arrayListOf<Pair<String, String>>()
    val xpathFactory = XPathFactory.instance()
    val nodes: List<FBDNode>

    init {
        val nodes = xpathFactory.compile("./body/FBD/block", Filters.element()).evaluate(e)
                .map { translateBlock(it) }

        nodes.forEach { n ->
            n.predessorBlocks = n.connectionIn.mapNotNull { ref -> nodes.find { it.id == ref } }
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

    //private val connectionInIds = xpathFactory.compile("//connectionPointIn/connection@refLocalId", Filters.attribute())
    private val inVar = xpathFactory.compile("./inputVariables/variable", Filters.element())

    fun run() {
        writer.nl().printf("VAR").block {
            nodes.filter { !it.callTypeIsFunction }
                    .forEach {
                        nl().printf("${it.instanceName} : ${it.type};")
                    }
        }
        writer.nl().printf("END_VAR").nl()

        nodes.forEach {
            writer.nl()
            if (it.callTypeIsFunction) {
                writer.printf("${it.assignTo} := ${it.type}")
            } else {
                writer.printf(it.instanceName)
            }

            it.inputVariables
                    .sortedWith(compareBy { it.first })
                    .joinTo(writer, ", ", "(", ");", -1)
                    { (formal, expr) ->
                        if (it.callTypeIsFunction) expr
                        else "$formal := $expr"
                    }
        }
        writer.nl()
    }

    private fun translateBlock(block: Element): FBDNode {
        val id = block.getAttributeValue("localId")
        val type = block.getAttributeValue("typeName")
        val iName = block.getAttributeValue("instanceName") ?: type.toLowerCase()
        val node = FBDNode(id, type)
        node.instanceName = iName
        //node.connectionIn.addAll(connectionInIds.evaluate(block).map { it.value })

        val ct = xpathFactory.compile(".//CallType", Filters.element()).evaluateFirst(block)
        node.callTypeIsFunction = ct != null && ct.textTrim == "function"

        inVar.evaluate(block).forEach {
            val formalParameter = it.getAttributeValue("formalParameter")
            val refTo = it.getChild("connectionPointIn").getChild("connection").getAttributeValue("refLocalId")
            node.connectionIn.add(refTo)
            val expr = getExpr(refTo)
            node.inputVariables += formalParameter to expr
        }

        if (node.callTypeIsFunction) {
            val findExpr = xpathFactory.compile("./body/FBD/outVariable[./connectionPointIn/connection[@refLocalId='${node.id}']]",
                    Filters.element())
            val outVar = findExpr.evaluateFirst(e)
            node.assignTo = outVar?.getChildText("expression")
        }

        return node
    }

    private fun getExpr(refTo: String): String {
        val findExpr = xpathFactory.compile("./body/FBD/inVariable[@localId='$refTo']", Filters.element())
        val a = findExpr.evaluateFirst(e)
        return a?.getChildText("expression") ?: ""
    }
}

data class FBDNode(
        val id: String,
        val type: String) {
    var instanceName: String = type.toLowerCase()
    val connectionIn = arrayListOf<String>()
    var predessorBlocks = listOf<FBDNode>()
    val inputVariables = arrayListOf<Pair<String, String>>()
    var callTypeIsFunction = false
    var assignTo: String? = null
    var executionOrder: Int = 0;
}