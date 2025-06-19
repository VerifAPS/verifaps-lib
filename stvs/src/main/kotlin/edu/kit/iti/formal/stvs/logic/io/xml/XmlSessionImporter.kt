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
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.code.Code
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.History
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.HybridSpecification
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario
import org.jdom2.Element
import tornadofx.asObservable
import java.io.File
import java.io.IOException
import java.net.URL

/**
 * This class provides the functionality to import whole sessions ([StvsRootModel]s) from
 * xml nodes.
 *
 * @author Benjamin Alt
 */
class XmlSessionImporter(currentConfig: GlobalConfig, currentHistory: History) : XmlImporter<StvsRootModel>() {
    private val constraintSpecImporter = XmlConstraintSpecImporter()

    // private XmlConfigImporter configImporter;
    private val currentConfig: GlobalConfig
    private val currentHistory: History

    /**
     * Creates an Importer. `currentConfig` and `currentHistory` are later passed to the
     * new [StvsRootModel].
     *
     * @param currentConfig currently used configuration
     * @param currentHistory currently used history
     * @throws ImportException Exception while importing
     */
    init {
        // configImporter = new XmlConfigImporter();
        this.currentConfig = currentConfig
        this.currentHistory = currentHistory
    }

    /**
     * Imports a [StvsRootModel] from `source`.
     *
     * @param source Node to import
     * @return imported model
     * @throws ImportException Exception while importing.
     */
    @Throws(ImportException::class)
    override fun doImportFromXmlNode(source: Element): StvsRootModel {
        // Code
        val code = Code()
        code.updateSourcecode(source.getChild("code").getChildText("plaintext"))
        val scenario = VerificationScenario()
        scenario.code = code

        val typeContext = code.parsedCode?.let { it.definedTypes } ?: listOf(TypeInt, TypeBool)

        // Tabs
        val hybridSpecs: List<HybridSpecification> = importTabs(source, typeContext)

        return StvsRootModel(
            hybridSpecs.asObservable(),
            currentConfig,
            currentHistory,
            scenario,
            File(System.getProperty("user.home")),
            "",
        )
    }

    /**
     * Imports tabs from [Session].
     *
     * @param importedSession session from which tabs should be imported
     * @param typeContext type context that should be used for the [XmlConcreteSpecImporter]
     * @return list of imported specifications (tabs)
     * @throws ImportException Exception while importing
     */
    @Throws(ImportException::class)
    private fun importTabs(importedSession: Element, typeContext: List<Type>): List<HybridSpecification> {
        val concreteSpecImporter = XmlConcreteSpecImporter(typeContext)
        val hybridSpecs: MutableList<HybridSpecification> = ArrayList<HybridSpecification>()
        for (tab in importedSession.getChild("tabs").getChildren("tab")) {
            var hybridSpec: HybridSpecification? = null
            var counterExample: ConcreteSpecification? = null
            var concreteInstance: ConcreteSpecification? = null
            val readOnly = tab.getAttributeValue("readOnly").toBoolean()
            for (specTable in tab.getChildren("specification")) {
                val concrete = specTable.getAttributeValue("isConcrete").toBoolean()

                if (!concrete) {
                    if (hybridSpec != null) {
                        throw ImportException("Tab may not have more than one abstract specification")
                    }
                    val constraintSpec = constraintSpecImporter.doImportFromXmlNode(specTable)
                    hybridSpec = HybridSpecification(constraintSpec, !readOnly)
                } else {
                    val concreteSpec = concreteSpecImporter.doImportFromXmlNode(specTable)
                    if (concreteSpec.isCounterExample) {
                        counterExample = concreteSpec
                    } else {
                        concreteInstance = concreteSpec
                    }
                }
            }
            if (hybridSpec == null) {
                throw ImportException("Tab must have at least one abstract specification")
            }
            hybridSpec.counterExample = counterExample
            hybridSpec.concreteInstance = concreteInstance
            hybridSpecs.add(hybridSpec)
        }
        return hybridSpecs
    }

    @get:Throws(IOException::class)
    override val xsdResource: URL?
        get() = javaClass.getResource("/fileFormats/stvs-1.0.xsd")
}