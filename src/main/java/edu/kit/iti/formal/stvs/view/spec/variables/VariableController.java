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

    view.getVarNameField().setOnAction(this::handleTextFieldChanged);
    view.getTypeComboBox().getItems().addAll(codeTypes);
    if (codeTypes.size() > 0) {
      view.getTypeComboBox().getSelectionModel().select(0);
    }
    view.getTypeComboBox().setOnAction(this::handleTypeChanged);
  }

  private void handleTypeChanged(ActionEvent actionEvent) {
    System.out.println("Changed type: "
        + view.getTypeComboBox().getSelectionModel().getSelectedItem());
  }

  private void handleTextFieldChanged(ActionEvent actionEvent) {
    freeVariable.setName(view.getVarNameField().getText());
  }

  @Override
  public VariableView getView() {
    return view;
  }
}
