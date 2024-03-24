package edu.kit.iti.formal.stvs.view.menu;

import javafx.scene.Node;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;

/**
 * Created by leonk on 22.03.2017.
 */
public class WizardPage extends VBox {
  private String title;

  public WizardPage(String title) {
    super();
    this.title = title;
    setSpacing(20.0);
  }

  public WizardPage(String title, Node content) {
    this(title);
    getChildren().setAll(content);
  }

  public String getTitle() {
    return title;
  }

  public void setTitle(String title) {
    this.title = title;
  }
}
