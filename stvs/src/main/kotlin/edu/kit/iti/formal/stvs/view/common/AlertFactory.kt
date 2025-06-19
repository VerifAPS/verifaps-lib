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

import javafx.scene.control.Alert
import javafx.scene.control.Alert.AlertType
import javafx.scene.control.Label
import javafx.scene.control.TextArea
import javafx.scene.layout.GridPane
import javafx.scene.layout.Priority
import java.io.PrintWriter
import java.io.StringWriter

/**
 * Factory for creating alerts.
 *
 * @author Carsten Csiky
 */
object AlertFactory {
    /**
     * Create an alert for an exception with a custom title and description.
     *
     * @param exception The exception for which the alert should be created
     * @param title The title of the alert
     * @param description The description in the alert
     * @return The created alert
     */
    @JvmOverloads
    fun createAlert(
        exception: Exception,
        title: String? = "Exception",
        description: String? = "An exception occured"
    ): Alert {
        // Write stack trace to string
        val sw = StringWriter()
        val pw = PrintWriter(sw)
        exception.printStackTrace(pw)
        val stackTrace = sw.toString()
        println(stackTrace)
        return createAlert(
            AlertType.ERROR, title, description, exception.message /*
          // Decided in Issue https://github.com/VerifAPS/stvs/issues/20, that the expandable content
          // should not be shown, instead it should be just logged
        , stackTrace
        // */
        )
    }

    /**
     * Create an alert with a given type, title, desciption and content text, but without expandable
     * content.
     *
     * @param type The type of the alert
     * @param title The title of the alert
     * @param description The description in the alert
     * @param content The content text for the alert
     * @return The created alert
     */
    fun createAlert(
        type: AlertType, title: String?, description: String?,
        content: String?
    ): Alert = createAlert(type, title, description, content, null)

    /**
     * Create an alert with a given type, title, desciption, content text and expandable content.
     *
     * @param type The type of the alert
     * @param title The title of the alert
     * @param description The description in the alert
     * @param contentText The content text for the alert
     * @param expandableContent The expandable content in the alert. This parameter may be null
     * @return The created alert
     */
    fun createAlert(
        type: AlertType, title: String?, description: String?,
        contentText: String?, expandableContent: String?
    ): Alert {
        val alert = Alert(type)
        alert.title = title
        alert.headerText = description
        alert.contentText = contentText

        val textArea = TextArea(expandableContent)
        textArea.isEditable = false
        textArea.isWrapText = true

        textArea.maxWidth = Double.MAX_VALUE
        textArea.maxHeight = Double.MAX_VALUE
        GridPane.setVgrow(textArea, Priority.ALWAYS)
        GridPane.setHgrow(textArea, Priority.ALWAYS)

        if (expandableContent != null && expandableContent.length > 0) {
            val expContent = GridPane()
            expContent.maxWidth = Double.MAX_VALUE
            if (type == AlertType.ERROR) {
                val label = Label("Stack trace:")
                expContent.add(label, 0, 0)
            }
            expContent.add(textArea, 0, 1)
            alert.dialogPane.expandableContent = expContent
        }

        if (type == AlertType.ERROR && expandableContent != null) {
            System.err.println(contentText)
            System.err.println(expandableContent)
        }

        alert.dialogPane.id = "AlertDialogPane_$type"

        return alert
    }
}