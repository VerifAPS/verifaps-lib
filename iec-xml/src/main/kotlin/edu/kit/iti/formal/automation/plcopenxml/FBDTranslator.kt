package edu.kit.iti.formal.automation.plcopenxml

import edu.kit.iti.formal.util.CodeWriter
import org.jdom2.Element
import org.jdom2.filter.Filters
import org.jdom2.xpath.XPathFactory

class FBDTranslator(val e: Element, val writer: CodeWriter) {
    val blockVariables = arrayListOf<Pair<String, String>>()
    val xpathFactory = XPathFactory.instance()

    val nodes = arrayListOf<FBDNode>()

    //private val connectionInIds = xpathFactory.compile("//connectionPointIn/connection@refLocalId", Filters.attribute())
    private val inVar = xpathFactory.compile("./inputVariables/variable", Filters.element())

    fun run() {
        val blocks = xpathFactory.compile("./body/FBD/block", Filters.element()).evaluate(e)
        for (block in blocks) {
            translateBlock(block)
        }

        writer.printf("VAR").block {
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
                    .joinTo(writer, ", ", "(", ");", -1) { (formal, expr) ->
                        if (it.callTypeIsFunction) expr
                        else "$formal := $expr"
                    }
        }
        writer.nl()
    }

    private fun translateBlock(block: Element) {
        val id = block.getAttributeValue("localId")
        val type = block.getAttributeValue("typeName")
        val iName = block.getAttributeValue("instanceName") ?: type.toLowerCase()
        val node = FBDNode(id, type)
        node.instanceName = iName
        nodes.add(node)
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
    }


    private fun getExpr(refTo: String): String {
        val findExpr = xpathFactory.compile("./body/FBD/inVariable[@localId='$refTo']", Filters.element())
        val a = findExpr.evaluateFirst(e)
        return a?.getChildText("expression") ?: ""
    }
}

data class FBDNode(
        val id: String,
        val type: String
) {
    var instanceName: String = type.toLowerCase()
    val connectionIn = arrayListOf<String>()
    val inputVariables = arrayListOf<Pair<String, String>>()
    var callTypeIsFunction = false
    var assignTo: String? = null
}