package edu.kit.iti.formal.stvs.model.config

import edu.kit.iti.formal.stvs.logic.io.ExecutableLocator
import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import javafx.beans.property.*
import kotlinx.serialization.*
import tornadofx.getValue
import tornadofx.setValue
import java.io.IOException
import java.nio.file.Paths
import kotlin.io.path.*



/**
 * Contains global configuration specified by the user.
 *
 * @author Benjamin Alt
 */
@Serializable
class GlobalConfig {
    val validLanguages: List<String> = mutableListOf("EN")

    // General
    @Transient
    val verificationTimeoutProperty: IntegerProperty = SimpleIntegerProperty(3600)

    /**
     * Set the verification timeout in milliseconds.
     * It must be a nonzero positive number.
     *
     * @param verificationTimeout a positive, nonzero integer that is the timeout in milliseconds
     * @throws IllegalArgumentException if the given integer is negative or zero
     */
    var verificationTimeout by verificationTimeoutProperty

    @Transient
    val simulationTimeoutProperty: IntegerProperty = SimpleIntegerProperty(60)
    var simulationTimeout by simulationTimeoutProperty

    @Transient
    val windowMaximizedProperty: BooleanProperty = SimpleBooleanProperty(true)
    var windowMaximized by windowMaximizedProperty

    @Transient
    val windowHeightProperty: IntegerProperty = SimpleIntegerProperty(600)
    var windowHeight by windowHeightProperty

    @Transient
    val windowWidthProperty: IntegerProperty = SimpleIntegerProperty(800)
    var windowWidth by windowWidthProperty

    @Transient
    val uiLanguageProperty: StringProperty = SimpleStringProperty("EN")
    var uiLanguage by uiLanguageProperty

    @Transient
    val maxLineRolloutProperty: IntegerProperty = SimpleIntegerProperty(50)
    var maxLineRollout by maxLineRolloutProperty

    // Editor
    @Transient
    val editorFontSizeProperty: IntegerProperty = SimpleIntegerProperty(12)
    var editorFontSize by editorFontSizeProperty

    @Transient
    val editorFontFamilyProperty: StringProperty = SimpleStringProperty("DejaVu Sans Mono")
    var editorFontFamily by editorFontFamilyProperty

    @Transient
    val showLineNumbersProperty: BooleanProperty = SimpleBooleanProperty(true)
    var showLineNumbers by showLineNumbersProperty

    // Dependency paths
    @Transient
    val nuxmvFilenameProperty: StringProperty = SimpleStringProperty(
        ExecutableLocator.findExecutableFileAsString("nuXmv")
            .orElse("[Path to nuXmv Executable]")
    )
    var nuxmvFilename by nuxmvFilenameProperty

    @Transient
    val z3PathProperty: StringProperty = SimpleStringProperty(
        ExecutableLocator.findExecutableFileAsString("z3")
            .orElse("[Path to Z3 Executable]")
    )
    var z3Path by z3PathProperty

    @Transient
    val getetaCommandProperty: StringProperty =
        SimpleStringProperty("java -jar /path/to/geteta.jar -c \${code} -t \${spec} -x")
    var getetaCommand by getetaCommandProperty

    /**
     * Tries to save this configuration to the path
     * <tt>[.CONFIG_DIRPATH]/[.AUTOLOAD_CONFIG_FILENAME]</tt>.
     *
     * @throws IOException if the file could not successfully be created
     * @throws ExportException if the file could not successfully be written / exported
     */
    @Throws(IOException::class, ExportException::class)
    fun autosaveConfig() {
        val configDir = CONFIG_DIRPATH
        if (!configDir.isDirectory() || !configDir.exists()) {
            configDir.createDirectories()
        }
        val configFile = CONFIG_DIRPATH / AUTOLOAD_CONFIG_FILENAME
        ExporterFacade.exportConfig(this, configFile)
    }

    /**
     * Replaces the contents of this GlobalConfig instance with those of a given GlobalConfig.
     * Preferred over a copy constructor because this method keeps listeners registered on the
     * properties, which will be notified about the changes.
     *
     * @param toBeCopied The GlobalConfig the contents of which will be copied
     */
    fun setAll(toBeCopied: GlobalConfig) {
        verificationTimeout = toBeCopied.verificationTimeout
        simulationTimeout = toBeCopied.simulationTimeout
        windowMaximized = toBeCopied.windowMaximized
        windowHeight = toBeCopied.windowHeight
        windowWidth = toBeCopied.windowWidth
        editorFontSize = toBeCopied.editorFontSize
        maxLineRollout = toBeCopied.maxLineRollout
        editorFontFamily = toBeCopied.editorFontFamily
        showLineNumbers = toBeCopied.showLineNumbers
        uiLanguage = toBeCopied.uiLanguage
        nuxmvFilename = toBeCopied.nuxmvFilename
        z3Path = toBeCopied.z3Path
        getetaCommand = toBeCopied.getetaCommand
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is GlobalConfig) return false

        if (validLanguages != other.validLanguages) return false
        if (verificationTimeoutProperty != other.verificationTimeoutProperty) return false
        if (simulationTimeoutProperty != other.simulationTimeoutProperty) return false
        if (windowMaximizedProperty != other.windowMaximizedProperty) return false
        if (windowHeightProperty != other.windowHeightProperty) return false
        if (windowWidthProperty != other.windowWidthProperty) return false
        if (uiLanguageProperty != other.uiLanguageProperty) return false
        if (maxLineRolloutProperty != other.maxLineRolloutProperty) return false
        if (editorFontSizeProperty != other.editorFontSizeProperty) return false
        if (editorFontFamilyProperty != other.editorFontFamilyProperty) return false
        if (showLineNumbersProperty != other.showLineNumbersProperty) return false
        if (nuxmvFilenameProperty != other.nuxmvFilenameProperty) return false
        if (z3PathProperty != other.z3PathProperty) return false
        if (getetaCommandProperty != other.getetaCommandProperty) return false

        return true
    }

    override fun hashCode(): Int {
        var result = validLanguages.hashCode()
        result = 31 * result + verificationTimeoutProperty.hashCode()
        result = 31 * result + simulationTimeoutProperty.hashCode()
        result = 31 * result + windowMaximizedProperty.hashCode()
        result = 31 * result + windowHeightProperty.hashCode()
        result = 31 * result + windowWidthProperty.hashCode()
        result = 31 * result + uiLanguageProperty.hashCode()
        result = 31 * result + maxLineRolloutProperty.hashCode()
        result = 31 * result + editorFontSizeProperty.hashCode()
        result = 31 * result + editorFontFamilyProperty.hashCode()
        result = 31 * result + showLineNumbersProperty.hashCode()
        result = 31 * result + nuxmvFilenameProperty.hashCode()
        result = 31 * result + z3PathProperty.hashCode()
        result = 31 * result + getetaCommandProperty.hashCode()
        return result
    }

    override fun toString(): String {
        return "GlobalConfig(validLanguages=$validLanguages, verificationTimeoutProperty=$verificationTimeoutProperty, simulationTimeoutProperty=$simulationTimeoutProperty, windowMaximizedProperty=$windowMaximizedProperty, windowHeightProperty=$windowHeightProperty, windowWidthProperty=$windowWidthProperty, uiLanguageProperty=$uiLanguageProperty, maxLineRolloutProperty=$maxLineRolloutProperty, editorFontSizeProperty=$editorFontSizeProperty, editorFontFamilyProperty=$editorFontFamilyProperty, showLineNumbersProperty=$showLineNumbersProperty, nuxmvFilenameProperty=$nuxmvFilenameProperty, z3PathProperty=$z3PathProperty, getetaCommandProperty=$getetaCommandProperty)"
    }


    companion object {
        const val AUTOLOAD_CONFIG_FILENAME: String = "stvs-config.json"
        val CONFIG_DIRPATH = Paths.get(System.getProperty("user.home"), ".config")

        /**
         * If the file at <tt>[.CONFIG_DIRPATH]/[.AUTOLOAD_CONFIG_FILENAME]</tt> exists,
         * it tries to load the configuration file. If it fails, it returns a default config
         * (see [.GlobalConfig]).
         *
         * @return the config from the default config file or a fresh default config
         */
        @JvmStatic
        fun autoloadConfig(): GlobalConfig {
            val configFile = CONFIG_DIRPATH / AUTOLOAD_CONFIG_FILENAME
            return try {
                ImporterFacade.importConfig(configFile)
            } catch (exception: Exception) {
                GlobalConfig()
            }
        }
    }
}
