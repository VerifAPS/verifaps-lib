package edu.kit.iti.formal.stvs.view.spec.table

import edu.kit.iti.formal.stvs.model.common.IoVariable
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable
import edu.kit.iti.formal.stvs.model.common.VariableCategory
import edu.kit.iti.formal.stvs.model.common.VariableRole
import edu.kit.iti.formal.stvs.model.expressions.VariableExpr
import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.beans.binding.Bindings
import javafx.beans.binding.BooleanBinding
import javafx.collections.FXCollections
import javafx.scene.control.ComboBox
import javafx.scene.control.Label
import javafx.scene.control.TextField
import javafx.scene.layout.GridPane

/**
 * The pane for configuring an i/o variable for use in the specification table view. This pane is
 * a component of the [IoVariableChooserDialog].
 *
 * @author Philipp
 */
class IoVariableDefinitionPane @JvmOverloads constructor(
    initialCategory: VariableCategory? = VariableCategory.INPUT,
    initialRole: VariableRole? = VariableRole.ASSUME,
    initialName: String? = "",
    initialType: String? = ""
) : GridPane() {
    val categoryComboBox: ComboBox<VariableCategory?>
    private val variableRoleComboBox: ComboBox<VariableRole>
    val nameTextField: TextField
    val typeTextField: TextField

    /**
     * Creates an instance with given default values to display.
     * @param initialCategory Default category
     * @param initialName Default name
     * @param initialType Default type
     */
    /**
     * Creates an instance for an input variable with empty name/type.
     */
    init {
        vgap = 10.0
        hgap = 10.0

        this.categoryComboBox = ComboBox(
            FXCollections.observableArrayList(*VariableCategory.entries.toTypedArray())
        )
        this.variableRoleComboBox = ComboBox(
            FXCollections.observableArrayList(*VariableRole.entries.toTypedArray())
        )
        this.nameTextField = TextField(initialName)
        this.typeTextField = TextField(initialType)

        categoryComboBox.valueProperty().set(initialCategory)

        add(Label("category: "), 0, 0)
        add(Label("verification-role: "), 0, 1)
        add(Label("name: "), 0, 2)
        add(Label("type: "), 0, 3)
        add(categoryComboBox, 1, 0)
        add(variableRoleComboBox, 1, 1)
        add(nameTextField, 1, 2)
        add(typeTextField, 1, 3)
        ViewUtils.setupClass(this)
    }

    /**
     * Sets the displayed values according to the values in a given variable.
     * @param ioVariable IO variable that holds the values which should be displayed
     */
    fun setFromIoVariable(ioVariable: IoVariable?) {
        categoryComboBox.valueProperty().set(ioVariable!!.category)
        variableRoleComboBox.valueProperty().set(ioVariable.category!!.defaultRole)
        nameTextField.text = ioVariable.name
        typeTextField.text = ioVariable.type
    }

    val definedVariable: SpecIoVariable
        /**
         * Generate a SpecIOVariable from this pane.
         * @return Generated variable
         */
        get() = SpecIoVariable(
            categoryComboBox.value!!, typeTextField.text,
            nameTextField.text
        )

    /**
     * Returns if the specified SpecIOVariable is invalid.
     * This includes that the defined name must not be present in
     * `alreadyDefinedVariables` for this function to return false.
     *
     * @param alreadyDefinedVariables check against this list if variable name is already present
     * @return Status if the specification is invalid
     */
    fun isDefinitionInvalid(alreadyDefinedVariables: List<SpecIoVariable?>?): Boolean {
        val chosenName = nameTextField.text
        val chosenType = typeTextField.text
        if (!VariableExpr.IDENTIFIER_PATTERN.matcher(chosenName).matches()
            || !VariableExpr.IDENTIFIER_PATTERN.matcher(chosenType).matches()
        ) {
            return true
        }
        return alreadyDefinedVariables!!.stream()
            .anyMatch { `var`: SpecIoVariable? -> `var`!!.name.equals(chosenName) }
    }

    /**
     * Returns a self updating binding to check if the definition is invalid
     * @param alreadyDefinedVariables check against this list if variable name is already present
     * @return binding that always represents the return value of
     * [IoVariableDefinitionPane.isDefinitionInvalid].
     */
    fun createDefinitionInvalidBinding(
        alreadyDefinedVariables: List<SpecIoVariable?>?
    ): BooleanBinding {
        return Bindings.createBooleanBinding(
            { isDefinitionInvalid(alreadyDefinedVariables) },
            nameTextField.textProperty(),
            typeTextField.textProperty()
        )
    }

    /**
     * Write the made changes to a variable.
     *
     * @param variableToChange Variable to write to
     */
    fun applyChangesToVariable(variableToChange: SpecIoVariable) {
        variableToChange.category = categoryComboBox.value!!
        variableToChange.name = nameTextField.text
        variableToChange.type = typeTextField.text
    }
}
