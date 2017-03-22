package edu.kit.iti.formal.stvs.view.menu;

import javafx.scene.layout.AnchorPane;

/**
 * Created by leonk on 22.03.2017.
 */
public class WizardPage extends AnchorPane {
  private String title;

  public WizardPage(String title) {
    this.title = title;
  }

  public String getTitle() {
    return title;
  }

  public void setTitle(String title) {
    this.title = title;
  }
}
