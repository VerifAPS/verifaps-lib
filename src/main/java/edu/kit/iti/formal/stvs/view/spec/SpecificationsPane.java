package edu.kit.iti.formal.stvs.view.spec;

import javafx.collections.ObservableList;
import javafx.geometry.Insets;
import javafx.scene.control.Button;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.layout.AnchorPane;

/**
 * Created by csicar on 07.02.17.
 */
public class SpecificationsPane extends AnchorPane {
  private TabPane tabPane;
  private Button addButton;

  public SpecificationsPane() {
    this.tabPane = new TabPane();
    this.addButton = new Button("+");


    AnchorPane.setTopAnchor(tabPane, 5.0);
    AnchorPane.setLeftAnchor(tabPane, 5.0);
    AnchorPane.setRightAnchor(tabPane, 5.0);
    AnchorPane.setBottomAnchor(tabPane, 5.0);
    AnchorPane.setTopAnchor(addButton, 10.0);
    AnchorPane.setRightAnchor(addButton, 10.0);

    this.getChildren().addAll(tabPane, addButton);

  }

  public ObservableList<Tab> getTabs() {
    return tabPane.getTabs();
  }

  public TabPane getTabPane() {
    return tabPane;
  }

  public Button getAddButton() {
    return addButton;
  }

  public void onTabAdded(Runnable listener) {
    addButton.setOnAction(actionEvent -> {
      listener.run();
    });
  }

}
