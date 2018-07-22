package edu.kit.iti.formal.automation.plcopenxml

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.st.RefTo
import edu.kit.iti.formal.automation.st.ast.EnumerationTypeDeclaration
import edu.kit.iti.formal.automation.st.ast.SimpleTypeDeclaration
import edu.kit.iti.formal.automation.st.ast.StructureTypeDeclaration
import edu.kit.iti.formal.automation.st.util.CodeWriter
import org.antlr.v4.runtime.CommonToken
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
        val name = e.getAttributeValue("name")
        val td = StructureTypeDeclaration(name)

        writer.append("STRUCT")

        val q = xpathFactory.compile("$xpath/variable", Filters.element())
        for (variable in q.evaluate(e)) {
            val n = variable.getAttributeValue("name")
            val dt = VariableDeclXML.getDatatype(variable.getChild("type"))
            val doc = variable.getChild("documentation")?.getChild("xhtml")?.textTrim
            td.addField(n, SimpleTypeDeclaration(baseType = RefTo(dt)))
        }

        writer.append("END_STRUCT;")
    }
}

/**
 * Translates: dataTypes/dataType with ./baseType/enum
 */
object EnumTranslator : XMLTranslatorXPath("./baseType/enum") {
    override fun translate(e: Element, writer: CodeWriter) {
        val name = e.getAttributeValue("name")
        val td = EnumerationTypeDeclaration(name, RefTo(), null)
        val vq = xpathFactory.compile("$xpath/values/value@name", Filters.attribute())
        val values = vq.evaluate(e)
        for (a in values)
            td.addValue(CommonToken(IEC61131Lexer.IDENTIFIER, a.value))
    }
}