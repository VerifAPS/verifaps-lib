package edu.kit.iti.formal.stvs.view.menu

import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.view.ViewUtils
import edu.kit.iti.formal.stvs.view.common.FileSelectionField
import edu.kit.iti.formal.stvs.view.common.PositiveIntegerInputField
import edu.kit.iti.formal.stvs.view.menu.ConfigDialogManager
import javafx.geometry.Insets
import javafx.scene.control.*
import javafx.scene.layout.GridPane
import javafx.scene.text.Text

/**
 *
 *
 * The view for a config dialog. Includes numerous text fields, checkboxes and number text fields
 * that match the fields of a [edu.kit.iti.formal.stvs.model.config.GlobalConfig].
 *
 *
 *
 *
 * Created by csicar on 11.01.17.
 *
 *
 * @author Carsten Csiky
 */
class ConfigDialogPane : DialogPane() {
    val nuxmvFilename: FileSelectionField = FileSelectionField()
    val z3Path: FileSelectionField = FileSelectionField()
    val getetaCommand: TextField = TextField()
    val maxLineRollout: PositiveIntegerInputField = PositiveIntegerInputField()
    val verificationTimeout: PositiveIntegerInputField = PositiveIntegerInputField()
    val simulationTimeout: PositiveIntegerInputField = PositiveIntegerInputField()
    val editorFontSize: PositiveIntegerInputField = PositiveIntegerInputField()
    val editorFontFamily: TextField = TextField()
    val showLineNumbers: CheckBox = CheckBox()
    val uiLanguage: ComboBox<String?> = ComboBox()
    val okButtonType: ButtonType = ButtonType("Save", ButtonBar.ButtonData.OK_DONE)

    /**
     *
     *
     * Creates the view for a config dialog.
     *
     *
     *
     *
     * Text fields and checkboxes have to be initialized from a
     * [edu.kit.iti.formal.stvs.model.config.GlobalConfig] model. For that, use the
     * [ConfigDialogManager].
     *
     */
    init {
        this.buttonTypes.addAll(okButtonType, ButtonType.CANCEL)


        val grid = GridPane()
        grid.hgap = 10.0
        grid.vgap = 10.0
        grid.padding = Insets(20.0, 10.0, 10.0, 10.0)

        grid.add(Label("Verification Timeout"), 0, 0)
        grid.add(verificationTimeout, 1, 0)

        grid.add(Label("Simulation Timeout"), 0, 1)
        grid.add(simulationTimeout, 1, 1)

        grid.add(Label("Editor Fontsize"), 0, 2)
        grid.add(editorFontSize, 1, 2)

        grid.add(Label("Editor Font Family"), 0, 3)
        grid.add(editorFontFamily, 1, 3)

        grid.add(Label("Show Line Numbers"), 0, 4)
        grid.add(showLineNumbers, 1, 4)

        grid.add(Label("User Interface Language"), 0, 5)
        grid.add(uiLanguage, 1, 5)


        grid.add(Label("Path to NuXmv Executable"), 0, 6)
        grid.add(nuxmvFilename, 1, 6)


        grid.add(Label("Path to Z3"), 0, 7)
        grid.add(z3Path, 1, 7)

        grid.add(Label("GeTeTa Command"), 0, 9)
        grid.add(getetaCommand, 1, 9)
        val getetaCommandDescription =
            Text("Use \${code} and \${spec} for code and specification" + " filename substitution.")
        getetaCommandDescription.style = "-fx-font-style: italic"
        grid.add(getetaCommandDescription, 0, 10, 2, 1)

        grid.add(Label("Maximum Number of Rollouts per Line"), 0, 11)
        grid.add(maxLineRollout, 1, 11)
        this.content = grid
        ViewUtils.setupClass(this)
    }
}
