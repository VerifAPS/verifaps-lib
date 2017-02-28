package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.util.ListTypeConverter;

import java.util.List;

import javafx.beans.property.ObjectProperty;
import javafx.beans.value.ObservableValue;
import javafx.collections.ObservableList;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Dialog;
import javafx.scene.control.ListCell;
import javafx.scene.control.ListView;
import javafx.scene.control.SelectionMode;
import javafx.scene.control.TextField;
import javafx.scene.layout.VBox;

/**
 * @author Philipp
 */
public class IoVariableChooserDialog extends Dialog<SpecIoVariable> {

  private final TextField nameTextField;
  private final TextField typeTextField;
  private final IoVariableDefinitionPane definitionPane;
  private final ListView<CodeIoVariable> ioVariables;
  private final ButtonType createButton = new ButtonType("Create", ButtonBar.ButtonData.OK_DONE);

  public IoVariableChooserDialog(ObjectProperty<List<CodeIoVariable>> codeIoVariables,
      ObservableList<SpecIoVariable> alreadyDefinedVariables) {
    super();

    this.nameTextField = new TextField();
    this.typeTextField = new TextField();
    this.ioVariables = new ListView<>();
    this.definitionPane = new IoVariableDefinitionPane();

    ioVariables.getSelectionModel().setSelectionMode(SelectionMode.SINGLE);
    ioVariables.getSelectionModel().selectedItemProperty().addListener(this::onSelectionChanged);
    ioVariables.setCellFactory(this::createCellForListView);
    ioVariables.setItems(ListTypeConverter.makeObservableList(codeIoVariables));
    ioVariables.setPrefHeight(200);

    setResultConverter(this::convertResult);

    VBox box = new VBox(definitionPane, ioVariables);
    box.setSpacing(10);
    getDialogPane().setContent(box);
    getDialogPane().getButtonTypes().add(createButton);

    getDialogPane().lookupButton(createButton).disableProperty()
        .bind(definitionPane.createDefinitionInvalidBinding(alreadyDefinedVariables));
    getDialogPane().setId("IoVariableChooserDialogPane");
  }

  private ListCell<CodeIoVariable> createCellForListView(
      ListView<CodeIoVariable> codeIoVariableListView) {
    return new ListCell<CodeIoVariable>() {
      @Override
      protected void updateItem(CodeIoVariable item, boolean empty) {
        super.updateItem(item, empty);
        if (empty) {
          setText(null);
        } else {
          setText(item.getCategory() + " " + item.getName() + " : " + item.getType());
        }
      }
    };
  }

  private void onSelectionChanged(ObservableValue<? extends CodeIoVariable> obs, CodeIoVariable old,
      CodeIoVariable value) {
    definitionPane.setFromIoVariable(value);
  }

  private SpecIoVariable convertResult(ButtonType buttonType) {
    SpecIoVariable defined = definitionPane.getDefinedVariable();
    if (defined != null && buttonType == createButton) {
      return defined;
    } else {
      return null;
    }
  }
}
