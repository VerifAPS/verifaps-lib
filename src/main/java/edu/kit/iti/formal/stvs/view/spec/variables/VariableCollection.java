package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import javafx.scene.Node;
import javafx.scene.control.*;
import javafx.scene.layout.VBox;

/**
 * Created by csicar on 10.01.17.
 */
public class VariableCollection extends VBox {

  private final Label overviewLabel;
  private final ListView<FreeVariable> freeVariableListView;
  private final Button addFreeVariable;

  public VariableCollection() {
    this.overviewLabel = new Label("Free Variables:");
    this.addFreeVariable = new Button("Add Free Variable");
    this.freeVariableListView = new ListView<>();

    freeVariableListView.setEditable(true);
    freeVariableListView.getSelectionModel().setSelectionMode(SelectionMode.MULTIPLE);

    this.overviewLabel.getStyleClass().addAll("freevar", "overview-label");
    this.addFreeVariable.getStyleClass().addAll("freevar", "add-var-button");
    this.freeVariableListView.getStyleClass().addAll("freevar", "variable-list-view");

    this.getChildren().addAll(overviewLabel, freeVariableListView, addFreeVariable);
  }

  public Button getAddFreeVariable() {
    return addFreeVariable;
  }

  public ListView<FreeVariable> getFreeVariableListView() {
    return freeVariableListView;
  }

  public void removeVariableView(Node view) {
    this.getChildren().removeAll(view);
  }
}
