package edu.kit.iti.formal.stvs.view.menu

import edu.kit.iti.formal.stvs.logic.io.*
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.view.*
import edu.kit.iti.formal.stvs.view.common.AlertFactory
import javafx.beans.binding.BooleanBinding
import javafx.beans.property.BooleanProperty
import javafx.beans.property.IntegerProperty
import javafx.beans.property.ObjectProperty
import javafx.beans.property.StringProperty
import javafx.collections.FXCollections
import javafx.scene.control.*
import javafx.scene.control.Alert.AlertType
import javafx.util.Callback
import java.io.IOException

/**
 *
 *
 * The manager for the Config dialog view (with its model being the [GlobalConfig]).
 *
 *
 *
 *
 * Created by csicar on 11.01.17.
 *
 *
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
        view.uiLanguage.items = FXCollections.observableList(config.validLanguages)
        bind(view.verificationTimeout.textProperty(), config.verificationTimeoutProperty)
        bind(view.simulationTimeout.textProperty(), config.simulationTimeoutProperty)
        bind(view.editorFontFamily.textProperty(), config.editorFontFamilyProperty)
        bind(view.editorFontSize.textProperty(), config.editorFontSizeProperty)
        bind(view.showLineNumbers.selectedProperty(), config.showLineNumbersProperty)
        bind(view.uiLanguage.valueProperty(), config.uiLanguageProperty)
        bind(view.maxLineRollout.textProperty(), config.maxLineRolloutProperty)
        bind(view.nuxmvFilename.textField.textProperty(), config.nuxmvFilenameProperty)
        bind(view.z3Path.textField.textProperty(), config.z3PathProperty)
        bind(view.getetaCommand.textProperty(), config.getetaCommandProperty)

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
        config.showLineNumbers = (view.showLineNumbers.isSelected)
        config.simulationTimeout = (view.simulationTimeout.integer!!)
        config.verificationTimeout = (view.verificationTimeout.integer!!)
        config.uiLanguage = (view.uiLanguage.valueProperty().get()!!)
        config.maxLineRollout = (view.maxLineRollout.integer!!)
        config.nuxmvFilename = (view.nuxmvFilename.textField.text)
        config.z3Path = (view.z3Path.textField.text)
        config.getetaCommand = (view.getetaCommand.text)
        try {
            config.autosaveConfig()
        } catch (exception: IOException) {
            AlertFactory.createAlert(
                AlertType.ERROR, "Autosave error",
                "Error saving the current configuration",
                "The current configuration could not be saved.", exception.message
            ).showAndWait()
        } catch (exception: ExportException) {
            AlertFactory.createAlert(
                AlertType.ERROR, "Autosave error",
                "Error saving the current configuration",
                "The current configuration could not be saved.", exception.message
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
