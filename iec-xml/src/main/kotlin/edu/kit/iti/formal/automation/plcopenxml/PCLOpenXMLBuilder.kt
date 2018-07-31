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

import edu.kit.iti.formal.util.CodeWriter
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
import java.util.*

/**
 * Created by weigl on 23/06/14.
 */
class PCLOpenXMLBuilder(private val filename: File, private val writer: CodeWriter) {

    lateinit var document: Document

    val pous: List<Element> by lazy {
        val e = xpathFactory.compile("//pou", Filters.element())
        e.evaluate(document)
    }

    val dataTypes: List<Element> by lazy {
        val e = xpathFactory.compile("//dataType", Filters.element())
        e.evaluate(document)
    }

    @Throws(IOException::class, JDOMException::class)
    fun run() {
        document = loadXml()
        build()
    }

    @Throws(IOException::class, JDOMException::class)
    private fun loadXml(): Document {
        val saxBuilder = SAXBuilder()
        saxBuilder.saxHandlerFactory = FACTORY
        return saxBuilder.build(filename)
    }

    @Throws(JDOMException::class, IOException::class)
    fun build() {
        document.rootElement.namespace = Namespace.NO_NAMESPACE
        writer.append("// Extracted from %s on %s%n%n", filename, Date())
        DataTypeExtractor(dataTypes, writer).run()
        PouExtractor(pous, writer).run()
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
    }
}
