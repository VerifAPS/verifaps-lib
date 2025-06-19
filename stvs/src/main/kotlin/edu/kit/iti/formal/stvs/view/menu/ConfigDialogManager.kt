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
package edu.kit.iti.formal.stvs.view.menu

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.view.Controller
import edu.kit.iti.formal.stvs.view.common.AlertFactory
import javafx.beans.binding.BooleanBinding
import javafx.beans.property.*
import javafx.scene.control.Alert.AlertType
import javafx.scene.control.ButtonType
import javafx.scene.control.Dialog
import javafx.util.Callback
import java.io.IOException

/**
 * The manager for the Config dialog view (with its model being the [GlobalConfig]).
 * Created by csicar on 11.01.17.
 * @author Carsten Csiky
 */
class ConfigDialogManager(private val config: GlobalConfig) : Controller {
    override var view: ConfigDialogPane = ConfigDialogPane()
    private val dialog = Dialog<GlobalConfig?>()
    private val dialogValid: BooleanBinding

    /**
     * Creates the manager for the config dialog view. Here the model is bound to the view.
     * @param config the model to bind to the view
     */
    init {
        dialog.title = "Preferences"
        view = ConfigDialogPane()
        // set initial values
        bind(view.verificationTimeout.textProperty(), config.verificationTimeoutProperty)
        bind(view.simulationTimeout.textProperty(), config.simulationTimeoutProperty)
        bind(view.editorFontFamily.textProperty(), config.editorFontFamilyProperty)
        bind(view.editorFontSize.textProperty(), config.editorFontSizeProperty)
        bind(view.maxLineRollout.textProperty(), config.maxLineRolloutProperty)
        bind(view.nuxmvFilename.textField.textProperty(), config.nuxmvFilenameProperty)
        bind(view.z3Path.textField.textProperty(), config.z3PathProperty)

        dialogValid =
            view.verificationTimeout.validProperty().and(view.simulationTimeout.validProperty())
                .and(view.editorFontSize.validProperty()).and(view.maxLineRollout.validProperty())

        val button = view.lookupButton(view.okButtonType)
        button.disableProperty().bind(dialogValid.not())

        dialog.dialogPane = view
        dialog.resultConverter = Callback { buttonType: ButtonType -> this.convertResult(buttonType) }
    }

    private fun convertResult(buttonType: ButtonType): GlobalConfig? {
        if (buttonType != view.okButtonType) {
            return null
        }
        if (!dialogValid.get()) {
            return null
        }
        config.editorFontFamily = (view.editorFontFamily.text)
        config.editorFontSize = (view.editorFontSize.integer!!)
        config.simulationTimeout = (view.simulationTimeout.integer!!)
        config.verificationTimeout = (view.verificationTimeout.integer!!.toLong())
        config.maxLineRollout = (view.maxLineRollout.integer!!)
        config.nuxmvFilename = (view.nuxmvFilename.textField.text)
        config.z3Path = (view.z3Path.textField.text)
        try {
            config.autosaveConfig()
        } catch (exception: IOException) {
            AlertFactory.createAlert(
                AlertType.ERROR,
                "Autosave error",
                "Error saving the current configuration",
                "The current configuration could not be saved.",
                exception.message,
            ).showAndWait()
        } catch (exception: ExportException) {
            AlertFactory.createAlert(
                AlertType.ERROR,
                "Autosave error",
                "Error saving the current configuration",
                "The current configuration could not be saved.",
                exception.message,
            ).showAndWait()
        }
        return config
    }

    fun showAndWait() {
        dialog.showAndWait()
    }

    private fun bind(stringProperty: StringProperty, integerProperty: IntegerProperty) {
        stringProperty.set(integerProperty.value.toString())
    }

    private fun bind(stringProperty: StringProperty, integerProperty: LongProperty) {
        stringProperty.set(integerProperty.value.toString())
    }

    private fun bind(stringProperty: StringProperty, integerProperty: StringProperty) {
        stringProperty.set(integerProperty.get())
    }

    private fun bind(booleanProperty: BooleanProperty, booleanProperty2: BooleanProperty) {
        booleanProperty.set(booleanProperty2.get())
    }

    private fun bind(objectProperty: ObjectProperty<String?>, stringProperty: StringProperty) {
        objectProperty.set(stringProperty.get())
    }
}