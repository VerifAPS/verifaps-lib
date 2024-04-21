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
                    .setOmitDeclaration(false)
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
