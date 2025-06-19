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
package edu.kit.iti.formal.stvs.view.common

import javafx.stage.FileChooser
import java.io.File

/**
 * Factory for creating the appropriate FileChoosers (with the right titles, file extension filters,
 * etc.) for opening and saving files.
 *
 * @author Benjamin Alt
 */
object FileChooserFactory {
    /**
     * The file extension filters corresponding to the different FileTypes.
     */
    private val filters: MutableMap<FileType, FileChooser.ExtensionFilter>

    /**
     * The String representations of the different FileTypes.
     */
    private val typeIdentifiers: MutableMap<FileType, String>

    /*
     * Initialize the filters and typeIdentifiers maps.
     */
    init {
        filters = HashMap()
        filters[FileType.SPECIFICATION] =
            FileChooser.ExtensionFilter("Specification files " + "(*.xml)", "*.xml")
        filters[FileType.CODE] =
            FileChooser.ExtensionFilter("Structured Text files (*.st)", "*.st")
        filters[FileType.SESSION] =
            FileChooser.ExtensionFilter("Session files (*.xml)", "*.xml")
        filters[FileType.ANY] = FileChooser.ExtensionFilter(
            "ST Verification Studio files (*" + ".st, *.xml)",
            "*.st",
            "*.xml",
        )

        typeIdentifiers = HashMap()
        typeIdentifiers[FileType.SPECIFICATION] = "Specification"
        typeIdentifiers[FileType.CODE] = "Code"
        typeIdentifiers[FileType.SESSION] = "Session"
        typeIdentifiers[FileType.ANY] = "File"
    }

    /**
     * Create a new FileChooser for opening files.
     *
     * @param type The type of file to open
     * @param workingdir The directory the FileChooser opens initially
     * @return An appropriate FileChooser for opening the given type of file
     */
    fun createOpenFileChooser(type: FileType, workingdir: File?): FileChooser =
        createFileChooser(workingdir, "Open " + typeIdentifiers[type], filters[type])

    /**
     * Create a new FileChooser for saving files.
     *
     * @param type The type of file to save
     * @param workingdir The directory the FileChooser opens initially
     * @return An appropriate FileChooser for saving the given type of file
     */
    fun createSaveFileChooser(type: FileType, workingdir: File?): FileChooser =
        createFileChooser(workingdir, "Save " + typeIdentifiers[type], filters[type])

    /**
     * Create a new FileChooser with a given working directory, title and extension filter.
     *
     * @param workingdir The directory the FileChooser opens initially
     * @param title The FileChooser window title
     * @param filter The extension filter for the FileChooser
     * @return A FileChooser with the desired characteristics
     */
    fun createFileChooser(workingdir: File?, title: String?, filter: FileChooser.ExtensionFilter?): FileChooser {
        val fileChooser = FileChooser()
        fileChooser.title = title
        fileChooser.extensionFilters.addAll(filter)
        fileChooser.initialDirectory = workingdir
        return fileChooser
    }

    /**
     * The type of file for which a dialog should be created.
     */
    enum class FileType {
        SPECIFICATION,
        SESSION,
        CODE,
        ANY,
    }
}