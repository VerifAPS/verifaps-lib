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
        val config: GlobalConfig = GlobalConfig()
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
        if (deps != null) {
            if (deps.getChildText("getetaCommand") != null) {
                config.getetaCommand = deps.getChildText("getetaCommand")
            }
            if (deps.getChildText("nuxmvFilename") != null) {
                config.nuxmvFilename = deps.getChildText("nuxmvFilename")
            }
            if (deps.getChildText("z3Path") != null) {
                config.z3Path = deps.getChildText("z3Path")
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
        if (general != null) {
            if (general.getChildText("uiLanguage") != null) {
                config.uiLanguage = general.getChildText("uiLanguage")
            }
            if (general.getChildText("simulationTime") != null) {
                config.simulationTimeout = general.getChildText("simulationTimeout").toInt()
            }
            if (general.getChildText("verificationTimeout") != null) {
                config.verificationTimeout = general.getChildText("verificationTimeout").toInt()
            }
            general.getChild("windowSize")?.let { windowSize ->
                if (windowSize.getChildText("height") != null) {
                    config.windowHeight = windowSize.getChildText("height").toInt()
                }
                if (windowSize.getChildText("width") != null) {
                    config.windowWidth = windowSize.getChildText("width").toInt()
                }
                if (windowSize.getChildText("maximized") != null) {
                    config.windowMaximized = windowSize.getChildText("maximized").toBoolean()
                }
            }
            if (general.getChildText("maxLineRollout") != null) {
                config.maxLineRollout = general.getChildText("maxLineRollout").toInt()
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
        if (editor != null) {
            if (editor.getChildText("fontSize") != null) {
                config.editorFontSize = editor.getChildText("fontSize").toInt()
            }
            if (editor.getChildText("fontFamily") != null) {
                config.editorFontFamily = editor.getChildText("fontFamily")
            }
            config.showLineNumbers = editor.getChildText("showLineNumbers") == "true"
        }
    }

    override val xsdResource: URL?
        get() = javaClass.getResource("/fileFormats/stvs-1.0.xsd")
}
