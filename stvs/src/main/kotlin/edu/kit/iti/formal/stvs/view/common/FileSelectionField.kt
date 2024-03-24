package edu.kit.iti.formal.stvs.view.common

import de.jensd.fx.glyphs.GlyphsDude
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon
import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.control.*
import javafx.scene.layout.*
import javafx.stage.FileChooser

/**
 * A text field with a button for choosing a file and displaying their path.
 *
 * @author Benjamin Alt
 */
class FileSelectionField : HBox() {
    val textField: TextField

    /**
     * Constructor.
     */
    init {
        spacing = 10.0
        ViewUtils.setupClass(this)
        textField = TextField()
        val fileSelectButton = GlyphsDude.createIconButton(FontAwesomeIcon.FOLDER_OPEN)
        children.add(textField)
        children.add(fileSelectButton)
        fileSelectButton.onAction =
            EventHandler { _: ActionEvent -> this.onFileSelectButtonClicked() }
        setHgrow(textField, Priority.ALWAYS)
    }

    private fun onFileSelectButtonClicked() {
        val fileChooser = FileChooser()
        fileChooser.title = "Select Executable"
        val selectedFile = fileChooser.showOpenDialog(scene.window)
        if (selectedFile != null) {
            textField.text = selectedFile.absolutePath
        }
    }
}
