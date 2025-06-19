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

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade
import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import javafx.beans.property.SimpleListProperty
import javafx.collections.FXCollections
import javafx.collections.ObservableList
import tornadofx.getValue
import tornadofx.setValue
import java.io.IOException
import java.nio.file.Files
import java.util.function.Consumer
import kotlin.io.path.div
import kotlin.io.path.exists
import kotlin.io.path.isDirectory

/**
 * Contains information about recently opened code and spec files.
 *
 * @author Benjamin Alt
 */
class History // Don't silently cut off the part of the input collection that doesn't fit
/**
 * Creates a history of recently opened files from the given collection.
 * The Collections' size must be less then or equal to [.HISTORY_DEPTH].
 *
 * @param filenames the most recently opened files.
 * @throws IllegalArgumentException if the given collection is bigger than [.HISTORY_DEPTH]
 */
(
    filenames: Collection<String> = listOf()
) {
    /**
     * Get the current file history.
     *
     * @return An ObservableList with the most recently opened filenames.
     */
    @Transient
    val filenamesProperty = SimpleListProperty(FXCollections.observableArrayList<String>())
    var filenames: ObservableList<String> by filenamesProperty

    init {
        require(filenames.size <= HISTORY_DEPTH) {
            // Don't silently cut off the part of the input collection that doesn't fit
            "List of filenames exceeds history size"
        }
        this.filenames.addAll(filenames)
    }

    /**
     * Add a filename to the history. If the file already exists inside this history, then
     * it gets reordered to the front of the history. If it is new and the history is full,
     * then the least recently opened file is deleted from the history.
     *
     * @param filename the file to store in the recently opened files history
     */
    fun addFilename(filename: String) {
        // Prevent entries from being added twice --> remove and add to the end ("most recent")
        if (filenames.contains(filename)) {
            filenames.remove(filename)
        }
        // Prevent filenames from getting larger than HISTORY_DEPTH
        val excess = filenames.size - HISTORY_DEPTH + 1
        if (excess > 0) {
            filenamesProperty.get().remove(0, excess)
        }
        filenames.add(filename)
    }

    /**
     * Tries to save this history as xml file to the default history file path
     * [GlobalConfig.CONFIG_DIRPATH]/[.AUTOLOAD_HISTORY_FILENAME].
     *
     * @throws IOException if the directories to the default path or the file could not be created
     * @throws ExportException if the history could not be written to the file
     */
    @Throws(IOException::class, ExportException::class)
    fun autosaveHistory() {
        val configDir = GlobalConfig.CONFIG_DIRPATH
        if (!configDir.isDirectory() || !configDir.exists()) {
            Files.createDirectories(configDir)
        }
        ExporterFacade.exportHistory(this, historyFile.toFile())
    }

    /**
     * Replaces the contents of this history instance with those of a given history. Preferred over a
     * copy constructor because this method keeps listeners registered on the properties, which will
     * be notified about the changes.
     *
     * @param history The history the contents of which will be copied
     */
    fun setAll(history: History) {
        history.filenames.forEach(Consumer { filename: String -> this.addFilename(filename) })
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is History) return false

        if (filenames != other.filenames) return false

        return true
    }

    override fun hashCode(): Int = filenames.hashCode()

    companion object {
        private const val AUTOLOAD_HISTORY_FILENAME = "stvs-history.xml"
        private val historyFile = GlobalConfig.CONFIG_DIRPATH / AUTOLOAD_HISTORY_FILENAME

        const val HISTORY_DEPTH: Int = 15

        /**
         * Loads an xml file from the default history path
         * [GlobalConfig.CONFIG_DIRPATH]/[.AUTOLOAD_HISTORY_FILENAME].
         * If this file does not exist or could not be read or parsed, a new history is returned.
         *
         * @return either the history stored at the default path or a new history
         */
        @JvmStatic
        fun autoloadHistory(): History = try {
                ImporterFacade.importHistory(historyFile.toFile())
            } catch (e: ImportException) {
                History()
            }
    }
}