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

  public IoVariableDefinitionPane() {
    this(VariableCategory.INPUT, "", "");
  }

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

  public void setFromIoVariable(IoVariable ioVariable) {
    this.categoryComboBox.valueProperty().set(ioVariable.getCategory());
    this.nameTextField.setText(ioVariable.getName());
    this.typeTextField.setText(ioVariable.getType());
  }

  public SpecIoVariable getDefinedVariable() {
    return new SpecIoVariable(categoryComboBox.getValue(), typeTextField.getText(),
        nameTextField.getText());
  }

  public TextField getNameTextField() {
    return nameTextField;
  }

  public Boolean isDefinitionInvalid(List<SpecIoVariable> alreadyDefinedVariables) {
    String chosenName = nameTextField.getText();
    String chosenType = typeTextField.getText();
    if (!VariableExpr.IDENTIFIER_PATTERN.matcher(chosenName).matches()
        || !VariableExpr.IDENTIFIER_PATTERN.matcher(chosenType).matches()) {
      return true;
    }
    return alreadyDefinedVariables.stream().anyMatch(var -> var.getName().equals(chosenName));
  }

  public BooleanBinding createDefinitionInvalidBinding(
      List<SpecIoVariable> alreadyDefinedVariables) {
    return Bindings.createBooleanBinding(() -> isDefinitionInvalid(alreadyDefinedVariables),
        nameTextField.textProperty(),
        typeTextField.textProperty());
  }

  public void applyChangesToVariable(SpecIoVariable variableToChange) {
    variableToChange.setCategory(categoryComboBox.getValue());
    variableToChange.setName(nameTextField.getText());
    variableToChange.setType(typeTextField.getText());
  }
}
