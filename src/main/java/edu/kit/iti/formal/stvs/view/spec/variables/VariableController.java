package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.scene.control.ContextMenu;

/**
 * Created by csicar on 10.01.17.
 */
public class VariableController implements Controller {
  private ObservableList<Type> codeTypes;
  private FreeVariable freeVariable;
  private VariableView view;
  private ContextMenu contextMenu;

  public VariableController(ObservableList<Type> codeTypes, FreeVariable freeVariable) {
    this.codeTypes = codeTypes;
    this.freeVariable = freeVariable;

    this.view = new VariableView(freeVariable);

    view.getVarNameField().setOnAction((e) -> handleTextFieldChanged());
    view.getVarNameField().focusedProperty().addListener((o, old, focused) -> {
      if (!focused) {
        handleTextFieldChanged();
      }
    });

    view.getTypeComboBox().getItems().addAll(codeTypes);
    view.getTypeComboBox().getSelectionModel().select(freeVariable.getType());
    view.getTypeComboBox().setOnAction(this::handleTypeChanged);
  }

  private void handleTypeChanged(ActionEvent actionEvent) {
    Type newType = view.getTypeComboBox().getSelectionModel().getSelectedItem();
    freeVariable.setType(newType);
  }

  private void handleTextFieldChanged() {
    try {
      freeVariable.setName(view.getVarNameField().getText());
    } catch (IllegalArgumentException exc) {
      System.err.println("Invalid name: " + exc.getMessage());
    }
  }

  @Override
  public VariableView getView() {
    return view;
  }
}
