package edu.kit.iti.formal.stvs.view.spec.table

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable
import javafx.beans.property.ListProperty
import javafx.beans.value.ObservableValue
import javafx.collections.ObservableList
import javafx.scene.control.*
import javafx.scene.layout.VBox
import javafx.util.Callback

/**
 * The dialog for configuring new i/o variables (i.e. adding columns) in a specification table.
 * @author Philipp
 */
class IoVariableChooserDialog(
    codeIoVariables: ListProperty<CodeIoVariable>,
    alreadyDefinedVariables: ObservableList<SpecIoVariable>
) : Dialog<SpecIoVariable?>() {
    private val nameTextField = TextField()
    private val typeTextField = TextField()
    private val definitionPane = IoVariableDefinitionPane()
    private val ioVariables = ListView<CodeIoVariable>()
    private val createButton = ButtonType("Create", ButtonBar.ButtonData.OK_DONE)

    /**
     * Creates an instance of a chooser dialog.
     * @param codeIoVariables variables that can be found in code
     * @param alreadyDefinedVariables variables already used in the table
     */
    init {
        ioVariables.selectionModel.selectionMode = SelectionMode.SINGLE
        ioVariables.selectionModel.selectedItemProperty()
            .addListener { obs, old: CodeIoVariable?, value: CodeIoVariable? ->
                this.onSelectionChanged(obs, old, value)
            }
        ioVariables.setCellFactory { codeIoVariableListView: ListView<CodeIoVariable?> ->
            this.createCellForListView(
                codeIoVariableListView
            )
        }
        val makeObservableList = codeIoVariables
        ioVariables.items = makeObservableList
        ioVariables.prefHeight = 200.0

        resultConverter = Callback { buttonType: ButtonType -> this.convertResult(buttonType) }

        val box = VBox(definitionPane, ioVariables)
        box.spacing = 10.0
        dialogPane.content = box
        dialogPane.buttonTypes.add(createButton)

        dialogPane.lookupButton(createButton).disableProperty()
            .bind(definitionPane.createDefinitionInvalidBinding(alreadyDefinedVariables))
        dialogPane.id = "IoVariableChooserDialogPane"
    }

    private fun createCellForListView(
        codeIoVariableListView: ListView<CodeIoVariable?>
    ): ListCell<CodeIoVariable?> {
        return object : ListCell<CodeIoVariable?>() {
            override fun updateItem(item: CodeIoVariable?, empty: Boolean) {
                super.updateItem(item, empty)
                text = if (empty) {
                    null
                } else {
                    item?.category.toString() + " " + item?.name + " : " + item?.type
                }
            }
        }
    }

    private fun onSelectionChanged(
        obs: ObservableValue<out CodeIoVariable?>, old: CodeIoVariable?,
        value: CodeIoVariable?
    ) {
        definitionPane.setFromIoVariable(value)
    }

    private fun convertResult(buttonType: ButtonType): SpecIoVariable? {
        val defined = definitionPane.definedVariable
        return if (defined != null && buttonType == createButton) {
            defined
        } else {
            null
        }
    }
}
