package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.geometry.Pos;
import javafx.scene.control.*;
import javafx.scene.control.SingleSelectionModel;
import javafx.scene.layout.HBox;

import javax.swing.*;

/**
 * Created by csicar on 10.01.17.
 */
public class VariableView extends HBox {

  private final TextField varNameField;
  private final Label hasTypeLabel;
  private final ComboBox<Type> typeComboBox;
  private final Button removeButton;

  public VariableView(FreeVariable variable) {
    this.varNameField = new TextField(variable.getName());
    this.hasTypeLabel = new Label(" : ");
    this.typeComboBox = new ComboBox<>();
    this.removeButton = new Button("Remove");

    varNameField.setAlignment(Pos.CENTER);
    varNameField.prefColumnCountProperty().bind(varNameField.textProperty().length().add(1));
    typeComboBox.setButtonCell(new TypeListCell());
    typeComboBox.setCellFactory(action -> new TypeListCell());

    getStylesheets().add(VariableView.class.getResource("style.css").toExternalForm());

    varNameField.getStyleClass().addAll("freevar", "name-field");
    hasTypeLabel.getStyleClass().addAll("freevar", "typeof-label");
    typeComboBox.getStyleClass().addAll("freevar", "type-combo-box");
    removeButton.getStyleClass().addAll("freevar", "remove-button");

    getChildren().addAll(varNameField, hasTypeLabel, typeComboBox, removeButton);
  }

  public TextField getVarNameField() {
    return varNameField;
  }

  public ComboBox<Type> getTypeComboBox() {
    return typeComboBox;
  }

  public Button getRemoveButton() {
    return removeButton;
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
