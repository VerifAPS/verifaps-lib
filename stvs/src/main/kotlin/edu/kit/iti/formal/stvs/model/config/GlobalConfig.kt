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
package edu.kit.iti.formal.stvs.model.config

import edu.kit.iti.formal.stvs.logic.io.ExecutableLocator
import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import javafx.beans.property.*
import tornadofx.getValue
import tornadofx.setValue
import java.io.IOException
import java.nio.file.Paths
import kotlin.io.path.createDirectories
import kotlin.io.path.div
import kotlin.io.path.exists
import kotlin.io.path.isDirectory

/**
 * Contains global configuration specified by the user.
 *
 * @author Benjamin Alt
 */
class GlobalConfig {
    val verificationTimeoutProperty: SimpleLongProperty = SimpleLongProperty(3600)

    /**
     * Set the verification timeout in milliseconds.
     * It must be a nonzero positive number.
     */
    var verificationTimeout by verificationTimeoutProperty

    val simulationTimeoutProperty: IntegerProperty = SimpleIntegerProperty(60)
    var simulationTimeout: Int by simulationTimeoutProperty

    val windowMaximizedProperty: BooleanProperty = SimpleBooleanProperty(true)
    var windowMaximized: Boolean by windowMaximizedProperty

    val windowHeightProperty: IntegerProperty = SimpleIntegerProperty(600)
    var windowHeight: Int by windowHeightProperty

    val windowWidthProperty: IntegerProperty = SimpleIntegerProperty(800)
    var windowWidth: Int by windowWidthProperty

    val maxLineRolloutProperty: IntegerProperty = SimpleIntegerProperty(50)
    var maxLineRollout: Int by maxLineRolloutProperty

    // Editor
    val editorFontSizeProperty: IntegerProperty = SimpleIntegerProperty(12)
    var editorFontSize: Int by editorFontSizeProperty

    val editorFontFamilyProperty: StringProperty = SimpleStringProperty("DejaVu Sans Mono")
    var editorFontFamily: String by editorFontFamilyProperty

    val nuxmvFilenameProperty: StringProperty = SimpleStringProperty(
        ExecutableLocator.findExecutableFileAsString("nuXmv") ?: "[Path to nuXmv Executable]",
    )
    var nuxmvFilename: String by nuxmvFilenameProperty

    val z3PathProperty: StringProperty = SimpleStringProperty(
        ExecutableLocator.findExecutableFileAsString("z3") ?: "[Path to Z3 Executable]",
    )
    var z3Path: String by z3PathProperty

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
        ExporterFacade.exportConfig(this, configFile.toFile())
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
        nuxmvFilename = toBeCopied.nuxmvFilename
        z3Path = toBeCopied.z3Path
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is GlobalConfig) return false

        if (verificationTimeout != other.verificationTimeout) return false
        if (simulationTimeout != other.simulationTimeout) return false
        if (windowMaximized != other.windowMaximized) return false
        if (windowHeight != other.windowHeight) return false
        if (windowWidth != other.windowWidth) return false
        if (maxLineRollout != other.maxLineRollout) return false
        if (editorFontSize != other.editorFontSize) return false
        if (editorFontFamily != other.editorFontFamily) return false
        if (nuxmvFilename != other.nuxmvFilename) return false
        if (z3Path != other.z3Path) return false
        return true
    }

    override fun hashCode(): Int {
        var result = verificationTimeout
        result = 31 * result + simulationTimeout
        result = 31 * result + windowMaximized.hashCode()
        result = 31 * result + windowHeight
        result = 31 * result + windowWidth
        result = 31 * result + maxLineRollout
        result = 31 * result + editorFontSize
        result = 31 * result + editorFontFamily.hashCode()
        result = 31 * result + nuxmvFilename.hashCode()
        result = 31 * result + z3Path.hashCode()
        return result.toInt()
    }

    companion object {
        const val AUTOLOAD_CONFIG_FILENAME: String = "stvs-config.xml"
        val CONFIG_DIRPATH = Paths.get(System.getProperty("user.home"), ".config", "stvs")

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
                ImporterFacade.importConfig(configFile.toFile())
            } catch (_: Exception) {
                GlobalConfig()
            }
        }
    }
}