package edu.kit.iti.formal.automation.plcopenxml

/*-
 * #%L
 * jpox
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.st.LookupList
import edu.kit.iti.formal.automation.st.ast.*
import org.jdom2.Document
import org.jdom2.Element
import org.jdom2.JDOMException
import org.jdom2.Namespace
import org.jdom2.filter.Filters
import org.jdom2.input.SAXBuilder
import org.jdom2.input.sax.SAXHandler
import org.jdom2.input.sax.SAXHandlerFactory
import org.jdom2.xpath.XPathFactory
import org.xml.sax.Attributes
import org.xml.sax.SAXException
import java.io.File
import java.io.IOException

/**
 * Created by weigl on 23/06/14.
 */
class PCLOpenXMLBuilder(private val filename: File) {
    private var document: Document? = null

    val poUs: Iterable<Element>
        get() {
            val e = xpathFactory.compile("//pou", Filters.element())
            return e.evaluate(document)

        }

    @Throws(IOException::class, JDOMException::class)
    protected fun loadXml(): Document {
        val saxBuilder = SAXBuilder()
        saxBuilder.saxHandlerFactory = FACTORY
        return saxBuilder.build(filename)
    }

    @Throws(JDOMException::class, IOException::class)
    fun build(): PouElements {
        document = loadXml()
        document!!.rootElement.namespace = Namespace.NO_NAMESPACE
        val ast = PouElements()
        for (e in poUs) {
            ast.add(buildPOU(e)!!)
        }
        return ast
    }

    companion object {
        /**
         * This handler ignores namespaces!
         */
        private val FACTORY = SAXHandlerFactory {
            object : SAXHandler() {
                @Throws(SAXException::class)
                override fun startElement(
                        namespaceURI: String?, localName: String?, qName: String?, atts: Attributes?) {
                    super.startElement("", localName, qName, atts)
                }

                @Throws(SAXException::class)
                override fun startPrefixMapping(prefix: String?, uri: String?) {
                    return
                }
            }
        }
        private val xpathFactory = XPathFactory.instance()

        private fun buildActions(e: Element): LookupList<ActionDeclaration> {
            val map = LookupList<ActionDeclaration>()
            val actions = xpathFactory.compile("./actions/action", Filters.element())
            val elements = actions.evaluate(e)
            for (action in elements) {
                val ad = buildAction(action)
                map.add(ad)
            }
            return map
        }

        private fun buildAction(action: Element): ActionDeclaration {
            val ad = ActionDeclaration()
            ad.name = action.getAttributeValue("name")
            ad.stBody = buildSTForPOU(action)
            ad.sfcBody = buildSFCForPOU(action)
            return ad
        }

        private fun buildPOU(e: Element): PouElement? {
            when (e.getAttributeValue("pouType")) {
                "functionBlock" -> return buildFunctionBlock(e)
                "program" -> return buildProgram(e)
                "function" -> return buildFunction(e)
            }
            return null
        }

        private fun buildFunction(e: Element): FunctionDeclaration {
            val fd = FunctionDeclaration()
            fd.name = e.getAttributeValue("name")
            fd.scope = InterfaceBuilder(e.getChild("interface")).get()
            fd.stBody = buildSTForPOU(e)!!
            //TODO how to find the return type fd.setReturnType();
            return fd
        }

        private fun buildFunctionBlock(e: Element): FunctionBlockDeclaration {
            val pd = FunctionBlockDeclaration()
            pd.name = e.getAttributeValue("name")
            pd.scope = InterfaceBuilder(e.getChild("interface")).get()
            pd.stBody = buildSTForPOU(e)
            pd.sfcBody = buildSFCForPOU(e)
            pd.actions = buildActions(e)
            return pd
        }

        private fun buildProgram(e: Element): ProgramDeclaration {
            val pd = ProgramDeclaration()
            pd.name = (e.getAttributeValue("name"))
            pd.scope = InterfaceBuilder(e.getChild("interface"))
                    .get()
            pd.stBody = buildSTForPOU(e)
            pd.sfcBody = buildSFCForPOU(e)
            pd.actions = buildActions(e)
            return pd
        }

        private fun buildSFCForPOU(e: Element): SFCImplementation? {
            val getSTBody = xpathFactory.compile("./body/SFC", Filters.element())
            val sfcElement = getSTBody.evaluateFirst(e)
            return if (sfcElement != null) {
                SFCFactory(sfcElement).get()
            } else null
        }

        private fun buildSTForPOU(e: Element): StatementList? {
            val getSTBody = xpathFactory.compile("./body/ST/xhtml/text()", Filters.text())
            val code = getSTBody.evaluateFirst(e)
            return if (code != null) {
                IEC61131Facade.statements(code.text)
            } else null
        }
    }
}
