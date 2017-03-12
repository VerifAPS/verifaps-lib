package edu.kit.iti.formal.stvs.view.spec;

import edu.kit.iti.formal.stvs.view.ViewUtils;
import javafx.collections.ObservableList;
import javafx.scene.control.Button;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.layout.AnchorPane;

/**
 * This Pane displays a collection of specifications as tabs.
 *
 * @author Carsten Csiky
 */
public class SpecificationsPane extends AnchorPane {
  private TabPane tabPane;
  private Button addButton;

  /**
   * Creates an empty instance.
   */
  public SpecificationsPane() {
    this.tabPane = new TabPane();
    this.addButton = new Button("+");
    ViewUtils.setupId(this);


    AnchorPane.setTopAnchor(tabPane, 0.0);
    AnchorPane.setLeftAnchor(tabPane, 0.0);
    AnchorPane.setRightAnchor(tabPane, 0.0);
    AnchorPane.setBottomAnchor(tabPane, 0.0);
    AnchorPane.setTopAnchor(addButton, 5.0);
    AnchorPane.setRightAnchor(addButton, 5.0);

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

  /**
   * Defines what should be invoked if a tab is added.
   * @param listener method to invoke
   */
  public void onTabAdded(Runnable listener) {
    addButton.setOnAction(actionEvent -> {
      listener.run();
    });
  }

}
