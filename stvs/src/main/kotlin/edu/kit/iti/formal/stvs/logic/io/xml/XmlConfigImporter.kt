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
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import org.jdom2.Element
import org.w3c.dom.Node
import java.net.URL

/**
 * This class provides the functionality to import a [GlobalConfig] from a xml node.
 *
 * @author Benjamin Alt
 */
class XmlConfigImporter : XmlImporter<GlobalConfig>() {
    /**
     * Imports a [GlobalConfig] from a xml [Node].
     *
     * @param source Xml node that should be imported
     * @return Imported config
     * @throws ImportException Exception while importing
     */
    @Throws(ImportException::class)
    override fun doImportFromXmlNode(source: Element): GlobalConfig {
        val config = GlobalConfig()
        setGeneralSettings(source.getChild("general"), config)
        setEditorSettings(source.getChild("editor"), config)
        setDependencies(source.getChild("dependencies"), config)
        return config
    }

    /**
     * Set the dependencies section of a given [GlobalConfig] according to an imported
     * [edu.kit.iti.formal.stvs.logic.io.xml.Config.Dependencies] object.
     *
     * @param deps   The imported dependencies
     * @param config The config to modify
     */
    private fun setDependencies(deps: Element?, config: GlobalConfig) {
        deps?.let {
            deps.getChildText("nuxmvFilename")?.let {
                config.nuxmvFilename = it
            }
            deps.getChildText("z3Path")?.let {
                config.z3Path = it
            }
        }
    }

    /**
     * Set the "general" section of a given [GlobalConfig] according to an imported
     * [edu.kit.iti.formal.stvs.logic.io.xml.Config.General] object.
     *
     * @param general The imported [edu.kit.iti.formal.stvs.logic.io.xml.Config.General] object
     * @param config  The config to modify
     */
    private fun setGeneralSettings(general: Element?, config: GlobalConfig) {
        general?.let {
            general.getChildText("simulationTimeout")?.let {
                config.simulationTimeout = it.toInt()
            }

            general.getChildText("verificationTimeout")?.let {
                config.verificationTimeout = it.toLong()
            }

            general.getChild("windowSize")?.let { windowSize ->
                windowSize.getChildText("height")?.let {
                    config.windowHeight = it.toInt()
                }
                windowSize.getChildText("width")?.let {
                    config.windowWidth = it.toInt()
                }
                windowSize.getChildText("maximized")?.let {
                    config.windowMaximized = it.toBoolean()
                }
            }
            general.getChildText("maxLineRollout")?.let {
                config.maxLineRollout = it.toInt()
            }
        }
    }

    /**
     * Set the "editor" section of a given [GlobalConfig] according to an imported
     * [edu.kit.iti.formal.stvs.logic.io.xml.Config.Editor] object.
     *
     * @param editor The imported [edu.kit.iti.formal.stvs.logic.io.xml.Config.Editor] object
     * @param config The config to modify
     */
    private fun setEditorSettings(editor: Element?, config: GlobalConfig) {
        editor?.let {
            editor.getChildText("fontSize")?.let {
                config.editorFontSize = it.toInt()
            }
            editor.getChildText("fontFamily")?.let {
                config.editorFontFamily = it
            }
        }
    }

    override val xsdResource: URL?
        get() = javaClass.getResource("/fileFormats/stvs-1.0.xsd")
}