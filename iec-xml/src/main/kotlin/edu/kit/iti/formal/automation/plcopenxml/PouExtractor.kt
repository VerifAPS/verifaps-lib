package edu.kit.iti.formal.automation.plcopenxml

import edu.kit.iti.formal.util.CodeWriter
import org.jdom2.Element
import org.jdom2.filter.Filters

class PouExtractor(val pous: List<Element>, val writer: CodeWriter,
                   val translators: List<XMLTranslator> = listOf<XMLTranslator>(
                           FunctionTranslator, FunctionBlockTranslator, ProgramTranslator)) {
    fun run() {
        val p = pous.sortedWith(compareBy({ it.getAttributeValue("pouType") }, { it.getAttributeValue("name") }))
        p.forEach { pou -> run(pou) }
    }

    fun run(pou: Element): Unit {
        translators.forEach { t ->
            if (t.isCapableOf(pou)) {
                t.translate(pou, writer)
                writer.nl().nl().nl()
                return
            }
        }
    }
}

object Actions : XMLTranslatorXPath("./actions") {
    override fun translate(e: Element, writer: CodeWriter) {
        val actions = xpathFactory.compile("$xpath/action", Filters.element())
        actions.evaluate(e).forEach {
            Action.translate(it, writer)
        }
    }
}

object Action : XMLTranslator {
    override fun isCapableOf(e: Element): Boolean = e.name == "action"
    override fun translate(e: Element, writer: CodeWriter) {
        writer.nl().printf("ACTION ${e.getAttributeValue("name")}").increaseIndent()
        STBody.translate(e, writer)
        SFCBody.translate(e, writer)
        writer.decreaseIndent().nl().printf("END_ACTION")
    }
}

abstract class POUTranslator(val type: String) : XMLTranslator {
    override fun isCapableOf(e: Element): Boolean =
            e.getAttributeValue("pouType") == type
}

object FunctionTranslator : POUTranslator("function") {
    override fun translate(e: Element, writer: CodeWriter) {
        val name = e.getAttributeValue("name")
        val returnType = VariableDeclXML.getDatatype(e.getChild("interface").getChild("returnType"))
        writer.printf("FUNCTION $name : $returnType")
                .increaseIndent().nl()
        InterfaceBuilder.translate(e, writer)
        STBody.translate(e, writer)
        FBDBody.translate(e, writer)
        writer.decreaseIndent().nl().printf("END_FUNCTION")
    }
}

object FunctionBlockTranslator : POUTranslator("functionBlock") {
    override fun translate(e: Element, writer: CodeWriter) {
        val name = e.getAttributeValue("name")
        writer.printf("FUNCTION_BLOCK $name").increaseIndent().nl()

        InterfaceBuilder.translate(e, writer)
        Actions.translate(e, writer)
        STBody.translate(e, writer)
        SFCBody.translate(e, writer)
        FBDBody.translate(e, writer)

        writer.decreaseIndent().nl().printf("END_FUNCTION_BLOCK").nl()
    }
}

object ProgramTranslator : POUTranslator("program") {
    override fun translate(e: Element, writer: CodeWriter) {
        val name = (e.getAttributeValue("name"))
        writer.printf("PROGRAM $name").increaseIndent().nl()

        InterfaceBuilder.translate(e, writer)
        Actions.translate(e, writer)
        STBody.translate(e, writer)
        SFCBody.translate(e, writer)
        FBDBody.translate(e, writer)

        writer.decreaseIndent().nl().printf("END_PROGRAM").nl()
    }
}


object SFCBody : XMLTranslatorXPath("./body/SFC") {
    override fun translate(e: Element, writer: CodeWriter) {
        val getSTBody = xpathFactory.compile("./body/SFC", Filters.element())
        val sfcElement = getSTBody.evaluateFirst(e)
        if (sfcElement != null) {
            SFCFactory(sfcElement, writer).run()
        }
    }
}

object STBody : XMLTranslatorXPath("./body/ST/xhtml") {
    override fun translate(e: Element, writer: CodeWriter) {
        val stBody = query.evaluateFirst(e)
        if (stBody != null)
            writer.nl().appendReformat(stBody.textTrim)
    }
}


object FBDBody : XMLTranslatorXPath("./body/FBD") {
    override fun translate(e: Element, writer: CodeWriter) {
        //FBDTranslator(e, writer).run()
    }
}