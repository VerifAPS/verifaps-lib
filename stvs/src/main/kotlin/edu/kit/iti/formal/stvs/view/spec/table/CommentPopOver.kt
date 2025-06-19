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
package edu.kit.iti.formal.stvs.view.spec.table

import edu.kit.iti.formal.stvs.view.spec.Lockable
import javafx.beans.property.BooleanProperty
import javafx.beans.property.SimpleBooleanProperty
import javafx.geometry.Insets
import javafx.scene.control.Button
import javafx.scene.control.ButtonBar
import javafx.scene.control.TextArea
import javafx.scene.layout.VBox
import org.controlsfx.control.PopOver
import org.kordamp.ikonli.fontawesome5.FontAwesomeSolid
import org.kordamp.ikonli.javafx.FontIcon

class CommentPopOver :
    PopOver(),
    Lockable {
    override val editableProperty: BooleanProperty = SimpleBooleanProperty(true)

    val textArea: TextArea = TextArea()

    private val buttonBar = ButtonBar()

    val saveButton: Button = Button(null, FontIcon(FontAwesomeSolid.SAVE))

    init {
        buttonBar.buttons.addAll(saveButton)
        val content = VBox(textArea, buttonBar)
        content.padding = Insets(5.0)
        this.title = "Edit Comment"
        this.contentNode = content
        textArea.editableProperty().bind(editableProperty)
    }
}