/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
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
 * *****************************************************************/
package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.io.Importer
import org.jdom2.Document
import org.jdom2.Element
import org.jdom2.input.JDOMParseException
import org.jdom2.input.SAXBuilder
import org.jdom2.input.sax.SAXHandler
import org.jdom2.input.sax.SAXHandlerFactory
import org.jdom2.input.sax.XMLReaderJDOMFactory
import org.jdom2.input.sax.XMLReaderXSDFactory
import org.xml.sax.Attributes
import org.xml.sax.SAXException
import java.io.IOException
import java.io.InputStream
import java.io.InputStreamReader
import java.io.Reader
import java.net.URL
import javax.xml.XMLConstants
import javax.xml.parsers.ParserConfigurationException
import javax.xml.transform.stream.StreamSource
import javax.xml.validation.SchemaFactory

/**
 * Common superclass for all Importers that import from xml.
 *
 * @author Benjamin Alt
 */
abstract class XmlImporter<T> : Importer<T> {
    /**
     * Checks that the given input matches the definition defined by `getXsdStream()`.
     *
     * @param xml Stream that holds the xml to be validated
     * @throws SAXException A general xml exception
     * @throws IOException  Error while communicating with IO while validating
     */
    @Throws(SAXException::class, IOException::class)
    private fun validateAgainstXsd(xml: InputStream) {
        val factory = SchemaFactory.newInstance(XMLConstants.W3C_XML_SCHEMA_NS_URI)
        val schema = factory.newSchema(xsdResource)
        val validator = schema.newValidator()
        validator.validate(StreamSource(xml))
    }

    /**
     * Imports an object from a xml input stream.
     *
     * @param source Stream that holds the xml to be validated
     * @return Imported object
     * @throws ImportException Exception while importing
     */
    @Throws(ImportException::class)
    override fun doImport(source: InputStream): T {
        try {
            val doc = readXml(source)
            return doImportFromXmlNode(doc.rootElement)
        } catch (e: SAXException) {
            e.printStackTrace()
            throw ImportException(e)
        } catch (e: IOException) {
            e.printStackTrace()
            throw ImportException(e)
        } catch (e: ParserConfigurationException) {
            e.printStackTrace()
            throw ImportException(e)
        } catch (e: JDOMParseException) {
            throw ImportException(e)
        } catch (e: RuntimeException) {
            throw ImportException(e)
        }
    }

    /**
     * Must be implemented by subclasses. This method must provide the logic to convert the given
     * `source` [Node] into the corresponding object.
     *
     * @param source Node to import
     * @return imported object
     * @throws ImportException Exception while importing
     */
    @Throws(ImportException::class)
    abstract fun doImportFromXmlNode(source: Element): T

    @get:Throws(IOException::class)
    protected abstract val xsdResource: URL?

    companion object {
        fun readXml(source: InputStream) = readXml(InputStreamReader(source))

        fun readXml(source: Reader): Document {
            val xsdResource = javaClass.getResource("/fileFormats/stvs-1.0.xsd")
            val factory = SAXHandlerFactory { _ ->
                object : SAXHandler() {
                    override fun startElement(
                        namespaceURI: String,
                        localName: String,
                        qName: String,
                        atts: Attributes,
                    ) = super.startElement("", localName, qName, atts)

                    override fun startPrefixMapping(prefix: String, uri: String) {
                    }
                }
            }

            val readerFactory: XMLReaderJDOMFactory = XMLReaderXSDFactory(xsdResource)
            val sax = SAXBuilder(readerFactory)
            assert(readerFactory.isValidating)

            sax.saxHandlerFactory = factory
            sax.setProperty(XMLConstants.ACCESS_EXTERNAL_DTD, "")
            sax.setProperty(XMLConstants.ACCESS_EXTERNAL_SCHEMA, "")
            return sax.build(source)
        }
    }
}