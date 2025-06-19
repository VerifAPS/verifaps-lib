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

import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.control.Button
import javafx.scene.control.TextField
import javafx.scene.layout.HBox
import javafx.scene.layout.Priority
import javafx.stage.FileChooser
import org.kordamp.ikonli.fontawesome5.FontAwesomeSolid
import org.kordamp.ikonli.javafx.FontIcon

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
        val fileSelectButton = Button(null, FontIcon(FontAwesomeSolid.FOLDER_OPEN))
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