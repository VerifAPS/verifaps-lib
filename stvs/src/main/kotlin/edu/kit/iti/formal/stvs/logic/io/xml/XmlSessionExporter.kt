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
    override fun exportToXmlNode(source: StvsRootModel): Element = xml("session", NAMESPACE) {
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