package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.util.ListTypeConverter;
import edu.kit.iti.formal.stvs.view.common.TypeComboBox;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ObservableValue;
import javafx.collections.FXCollections;
import javafx.scene.Node;
import javafx.scene.control.*;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;

import java.util.List;

import static javafx.scene.control.ButtonType.CANCEL;

public class IoVariableNameDialog extends Dialog<SpecIoVariable> {

  private final TextField nameTextField;
  private final TypeComboBox typeComboBox;
  private final ListView<CodeIoVariable> ioVariables;
  private final ButtonType createButton = new ButtonType("Create", ButtonBar.ButtonData.OK_DONE);

  public IoVariableNameDialog(ObjectProperty<List<Type>> typeContext,
                              ObjectProperty<List<CodeIoVariable>> codeIoVariables) {
    super();
    this.nameTextField = new TextField();
    // TODO: Update observable list of types (and of codeIoVariables)
    this.typeComboBox = new TypeComboBox(typeContext);
    this.ioVariables = new ListView<>();

    ioVariables.getSelectionModel().setSelectionMode(SelectionMode.SINGLE);
    ioVariables.getSelectionModel().selectedItemProperty().addListener(this::onSelectionChanged);
    ioVariables.setCellFactory(this::createCellForListView);
    ioVariables.setItems(ListTypeConverter.makeObservableList(codeIoVariables));
    ioVariables.setPrefHeight(200);

    setResultConverter(this::convertResult);

    getDialogPane().setContent(createContent());
    getDialogPane().getButtonTypes().add(createButton);

    updateButtonState(ioVariables.getSelectionModel().getSelectedItem());
  }

  private ListCell<CodeIoVariable> createCellForListView(ListView<CodeIoVariable> codeIoVariableListView) {
    return new ListCell<CodeIoVariable>() {
      @Override
      protected void updateItem(CodeIoVariable item, boolean empty) {
        super.updateItem(item, empty);
        if (empty) {
          setText(null);
        } else {
          setText(item.getCategory() + " " + item.getName() + " : " + item.getType().getTypeName());
        }
      }
    };
  }

  private void onSelectionChanged(ObservableValue<? extends CodeIoVariable> obs, CodeIoVariable old, CodeIoVariable value) {
    updateButtonState(value);
  }

  private void updateButtonState(CodeIoVariable selectedValue) {
    getDialogPane().lookupButton(createButton).setDisable(selectedValue == null);
  }

  private Node createContent() {
    return ioVariables; // TODO: Add gui for adding new variables
  }

  private SpecIoVariable convertResult(ButtonType buttonType) {
    CodeIoVariable selected = ioVariables.getSelectionModel().getSelectedItem();
    if (selected != null && buttonType == createButton) {
      return new SpecIoVariable(selected.getCategory(), selected.getType(), selected.getName());
    } else {
      return null;
    }
  }
}
