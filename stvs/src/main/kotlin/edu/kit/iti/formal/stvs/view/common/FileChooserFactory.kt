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
            "ST Verification Studio files (*" + ".st, *.xml)", "*.st", "*.xml"
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
    fun createOpenFileChooser(type: FileType, workingdir: File?): FileChooser {
        return createFileChooser(workingdir, "Open " + typeIdentifiers[type], filters[type])
    }

    /**
     * Create a new FileChooser for saving files.
     *
     * @param type The type of file to save
     * @param workingdir The directory the FileChooser opens initially
     * @return An appropriate FileChooser for saving the given type of file
     */
    fun createSaveFileChooser(type: FileType, workingdir: File?): FileChooser {
        return createFileChooser(workingdir, "Save " + typeIdentifiers[type], filters[type])
    }

    /**
     * Create a new FileChooser with a given working directory, title and extension filter.
     *
     * @param workingdir The directory the FileChooser opens initially
     * @param title The FileChooser window title
     * @param filter The extension filter for the FileChooser
     * @return A FileChooser with the desired characteristics
     */
    fun createFileChooser(
        workingdir: File?, title: String?,
        filter: FileChooser.ExtensionFilter?
    ): FileChooser {
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
        SPECIFICATION, SESSION, CODE, ANY
    }
}
