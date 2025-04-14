package edu.kit.iti.formal.stvs.logic.io.xml

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.model.StvsRootModel
import org.jdom2.CDATA
import org.jdom2.Element

/**
 * This class provides the functionality to export whole sessions, code and all specification tabs,
 * to xml. [XmlConstraintSpecExporter] and [XmlConcreteSpecExporter] are used to export
 * the specifications.
 *
 * @author Benjamin Alt
 */
class XmlSessionExporter : XmlExporter<StvsRootModel>() {
    // private XmlConfigExporter configExporter;
    // configExporter = new XmlConfigExporter();
    private val constraintSpecExporter = XmlConstraintSpecExporter()
    private val concreteSpecExporter = XmlConcreteSpecExporter()

    /**
     * Exports a [StvsRootModel] to xml.
     *
     * @param source Model that should be converted
     * @return Xml representing the session
     * @throws ExportException Exception while exporting
     */
    @Throws(ExportException::class)
    override fun exportToXmlNode(source: StvsRootModel): Element {
        return xml("session", NAMESPACE) {
            "code" {
                "plaintext" {
                    e.setContent(CDATA(source.scenario.code.sourcecode))
                }
                source.scenario.code.filename?.let { "fileName" { +it } }
            }
            "tabs" {
                // Tabs
                this.makeTabs(source)
            }
        }
    }

    /**
     * Extracts the tabs from the [StvsRootModel] and converts them into [Session.Tabs].
     *
     * @param source model to export the tabs from
     * @return exported tabs
     * @throws ExportException exception while exporting
     */
    @Throws(ExportException::class)
    private fun ElementBuilder.makeTabs(source: StvsRootModel) {
        source.hybridSpecifications.forEachIndexed { i, it ->
            "tab" {
                // One tab corresponds to one HybridSpecification
                set("id", i)
                set("open", false)
                set("readOnly", !it.isEditable)

                append(constraintSpecExporter.exportToXmlNode(it))

                val concreteSpecification = it.concreteInstance ?: it.counterExample
                if (concreteSpecification != null) {
                    append(concreteSpecExporter.exportToXmlNode(concreteSpecification))
                }
            }
        }
    }
}
