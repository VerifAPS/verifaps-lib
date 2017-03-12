package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IoVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.VariableExpr;
import edu.kit.iti.formal.stvs.view.ViewUtils;

import java.util.List;

import javafx.beans.binding.Bindings;
import javafx.beans.binding.BooleanBinding;
import javafx.collections.FXCollections;
import javafx.scene.control.ComboBox;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import javafx.scene.layout.GridPane;

/**
 * The pane for configuring an i/o variable for use in the specification table view. This pane is
 * a component of the {@link IoVariableChooserDialog}.
 *
 * @author Philipp
 */
public class IoVariableDefinitionPane extends GridPane {

  private final ComboBox<VariableCategory> categoryComboBox;
  private final TextField nameTextField;
  private final TextField typeTextField;

  /**
   * Creates an instance for an input variable with empty name/type.
   */
  public IoVariableDefinitionPane() {
    this(VariableCategory.INPUT, "", "");
  }

  /**
   * Creates an instance with given default values to display.
   * @param initialCategory Default category
   * @param initialName Default name
   * @param initialType Default type
   */
  public IoVariableDefinitionPane(VariableCategory initialCategory, String initialName,
      String initialType) {
    super();

    setVgap(10);
    setHgap(10);

    this.categoryComboBox = new ComboBox<>(
        FXCollections.observableArrayList(VariableCategory.INPUT, VariableCategory.OUTPUT));
    this.nameTextField = new TextField(initialName);
    this.typeTextField = new TextField(initialType);

    categoryComboBox.valueProperty().set(initialCategory);

    add(new Label("category: "), 0, 0);
    add(new Label("name: "), 0, 1);
    add(new Label("type: "), 0, 2);
    add(categoryComboBox, 1, 0);
    add(nameTextField, 1, 1);
    add(typeTextField, 1, 2);
    ViewUtils.setupId(this);
  }

  /**
   * Sets the displayed values according to the values in a given variable.
   * @param ioVariable IO variable that holds the values which should be displayed
   */
  public void setFromIoVariable(IoVariable ioVariable) {
    this.categoryComboBox.valueProperty().set(ioVariable.getCategory());
    this.nameTextField.setText(ioVariable.getName());
    this.typeTextField.setText(ioVariable.getType());
  }

  /**
   * Generate a SpecIOVariable from this pane.
   * @return Generated variable
   */
  public SpecIoVariable getDefinedVariable() {
    return new SpecIoVariable(categoryComboBox.getValue(), typeTextField.getText(),
        nameTextField.getText());
  }

  public TextField getNameTextField() {
    return nameTextField;
  }

  /**
   * Returns if the specified SpecIOVariable is invalid.
   * This includes that the defined name must not be present in
   * {@code alreadyDefinedVariables} for this function to return false.
   *
   * @param alreadyDefinedVariables check against this list if variable name is already present
   * @return Status if the specification is invalid
   */
  public Boolean isDefinitionInvalid(List<SpecIoVariable> alreadyDefinedVariables) {
    String chosenName = nameTextField.getText();
    String chosenType = typeTextField.getText();
    if (!VariableExpr.IDENTIFIER_PATTERN.matcher(chosenName).matches()
        || !VariableExpr.IDENTIFIER_PATTERN.matcher(chosenType).matches()) {
      return true;
    }
    return alreadyDefinedVariables.stream().anyMatch(var -> var.getName().equals(chosenName));
  }

  /**
   * Returns a self updating binding to check if the definition is invalid
   * @param alreadyDefinedVariables check against this list if variable name is already present
   * @return binding that always represents the return value of
   *  {@link IoVariableDefinitionPane#isDefinitionInvalid(List)}.
   */
  public BooleanBinding createDefinitionInvalidBinding(
      List<SpecIoVariable> alreadyDefinedVariables) {
    return Bindings.createBooleanBinding(() -> isDefinitionInvalid(alreadyDefinedVariables),
        nameTextField.textProperty(),
        typeTextField.textProperty());
  }

  /**
   * Write the made changes to a variable.
   *
   * @param variableToChange Variable to write to
   */
  public void applyChangesToVariable(SpecIoVariable variableToChange) {
    variableToChange.setCategory(categoryComboBox.getValue());
    variableToChange.setName(nameTextField.getText());
    variableToChange.setType(typeTextField.getText());
  }
}
