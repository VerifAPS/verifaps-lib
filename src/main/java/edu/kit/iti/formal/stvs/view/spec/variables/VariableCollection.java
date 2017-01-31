package edu.kit.iti.formal.stvs.view.spec.variables;

import javafx.scene.Node;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.layout.VBox;

/**
 * Created by csicar on 10.01.17.
 */
public class VariableCollection extends VBox {

  private final Label overviewLabel;
  private final Button addFreeVariable;

  public VariableCollection() {
    this.overviewLabel = new Label("Free Variables:");
    this.addFreeVariable = new Button("Add Free Variable");

    this.overviewLabel.getStyleClass().addAll("freevar", "overview-label");
    this.addFreeVariable.getStyleClass().addAll("freevar", "add-var-button");

    this.getChildren().addAll(overviewLabel, addFreeVariable);
  }

  public void addVariableView(Node view) {
    getChildren().add(getChildren().size() - 1, view);
  }

  public Button getAddFreeVariable() {
    return addFreeVariable;
  }

}
