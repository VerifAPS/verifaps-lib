package edu.kit.iti.formal.automation.plcopenxml

import edu.kit.iti.formal.util.CodeWriter
import org.jdom2.Element
import org.jdom2.filter.Filters
import org.jdom2.xpath.XPathFactory

/**
 *
 * @author Alexander Weigl
 * @version 1 (22.07.18)
 */

interface XMLTranslator {
    fun isCapableOf(e: Element): Boolean
    fun translate(e: Element, writer: CodeWriter)
}

interface XMLTranslatorFind {
    fun find(e: Element): Element?
    fun isCapableOf(e: Element): Boolean = find(e) != null
    fun translate(e: Element, writer: CodeWriter)
}


abstract class XMLTranslatorXPath(protected val xpath: String) : XMLTranslator {
    companion object {
        @JvmStatic
        protected val xpathFactory = XPathFactory.instance()
    }

    val query = xpathFactory.compile(xpath, Filters.element())
    override fun isCapableOf(e: Element): Boolean = query.evaluateFirst(e) != null
}


/**
 * Translates: dataTypes/dataType with ./baseType/struct
 */
object StructTranslator : XMLTranslatorXPath("./baseType/struct") {
    override fun translate(e: Element, writer: CodeWriter) {
        val q = xpathFactory.compile("$xpath/variable", Filters.element())

        val name = e.getAttributeValue("name")
        writer.nl().append("$name : STRUCT").increaseIndent()
        for (variable in q.evaluate(e)) {
            val n = variable.getAttributeValue("name")
            val dt = VariableDeclXML.getDatatype(variable.getChild("type"))
            val doc = variable.getChild("documentation")?.getChild("xhtml")?.textTrim
            if (doc != null) writer.nl().append("$n : $dt; (* $doc *)")
            else writer.nl().append("$n : $dt;")
        }

        writer.decreaseIndent().nl().append("END_STRUCT;")
    }
}

/**
 * Translates: dataTypes/dataType with ./baseType/enum
 */
object EnumTranslator : XMLTranslatorXPath("./baseType/enum") {
    override fun translate(e: Element, writer: CodeWriter) {
        val name = e.getAttributeValue("name")
        writer.nl().append("$name : ")
        val vq = xpathFactory.compile("$xpath/values/value/@name", Filters.attribute())
        val values = vq.evaluate(e)
        values.joinTo(writer, ", ", "(", ");") { it.value }
    }
}