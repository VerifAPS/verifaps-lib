package edu.kit.iti.formal.stvs.view.spec.variables;

import javafx.scene.control.Label;
import javafx.scene.layout.HBox;

/**
 * Created by csicar on 10.01.17.
 */
public class VariableView extends HBox {

  public VariableView() {
    this.getChildren().add(new Label("THIS IS MY VARIABLE"));
  }
}
