package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.scene.control.*;
import javafx.scene.layout.HBox;

/**
 * Created by csicar on 10.01.17.
 */
public class VariableView extends HBox {

  private final TextField varNameField;
  private final Label hasTypeLabel;
  private final ComboBox<Type> typeComboBox;

  public VariableView(FreeVariable variable) {
    this.varNameField = new TextField(variable.getName());
    this.hasTypeLabel = new Label(" : ");
    this.typeComboBox = new ComboBox<>();

    varNameField.setPromptText("identifier");
    typeComboBox.setButtonCell(new TypeListCell());
    typeComboBox.setCellFactory(action -> new TypeListCell());

    getStylesheets().add(VariableView.class.getResource("style.css").toExternalForm());

    varNameField.getStyleClass().addAll("freevar", "name-field");
    hasTypeLabel.getStyleClass().addAll("freevar", "typeof-label");
    typeComboBox.getStyleClass().addAll("freevar", "type-combo-box");

    getChildren().addAll(varNameField, hasTypeLabel, typeComboBox);
  }

  public TextField getVarNameField() {
    return varNameField;
  }

  public ComboBox<Type> getTypeComboBox() {
    return typeComboBox;
  }

  private class TypeListCell extends ListCell<Type> {
    TypeListCell() {
      getStyleClass().addAll("freevar", "type-combo-box-cell");
    }
    @Override
    public void updateItem(Type type, boolean empty) {
      super.updateItem(type, empty);
      if (empty) {
        setText("");
      } else {
        setText(type.getTypeName());
      }
    }
  }
}
