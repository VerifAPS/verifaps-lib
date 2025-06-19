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

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.logic.io.Exporter
import org.jdom2.Document
import org.jdom2.Element
import org.jdom2.Namespace
import org.jdom2.output.Format
import org.jdom2.output.XMLOutputter
import org.w3c.dom.Node
import java.io.OutputStream
import javax.xml.transform.TransformerException

/**
 * Common superclass for all Exporters that export to xml.
 *
 * @author Benjamin Alt
 */
abstract class XmlExporter<F> : Exporter<F> {
    /**
     * Exports an Object as xml.
     *
     * @param source Object to export
     * @return The output xml is written to this stream
     * @throws ExportException Exception while exporting
     */
    @Throws(ExportException::class)
    override fun export(source: F, target: OutputStream) {
        val xmlNode = exportToXmlNode(source)
        try {
            val xmlOutputter = XMLOutputter(
                Format.getPrettyFormat()
                    .setEncoding("UTF-8")
                    .setOmitEncoding(false)
                    .setOmitDeclaration(false),
            )
            xmlOutputter.output(Document(xmlNode), target)
        } catch (e: TransformerException) {
            throw ExportException(e)
        }
    }

    /**
     * Must be implemented by subclasses. This method must provide the logic to convert the given
     * `source` object into a xml [Node]
     *
     * @param source Element that should be converted
     * @return Xml node
     * @throws ExportException Exception while exporting
     */
    @Throws(ExportException::class)
    abstract fun exportToXmlNode(source: F): Element
}

const val NAMESPACE_URI = "http://formal.iti.kit.edu/stvs/io/1.0/"
val NAMESPACE = Namespace.getNamespace(NAMESPACE_URI)