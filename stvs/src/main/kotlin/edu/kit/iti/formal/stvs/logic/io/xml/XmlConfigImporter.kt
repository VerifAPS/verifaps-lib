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
            deps.getChildText("getetaCommand")?.let {
                config.getetaCommand = it
            }
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
            general.getChildText("uiLanguage")?.let {
                config.uiLanguage = general.getChildText("uiLanguage")
            }
            general.getChildText("simulationTime")?.let {
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
            config.showLineNumbers = editor.getChildText("showLineNumbers").toBoolean()
        }
    }

    override val xsdResource: URL?
        get() = javaClass.getResource("/fileFormats/stvs-1.0.xsd")
}
