package edu.kit.iti.formal.stvs.view.common;

import javafx.scene.control.Hyperlink;

/**
 * Created by csicar on 16.03.17.
 */
public class ActualHyperLink extends Hyperlink {

  private ActualHyperLink() {

  }

  public ActualHyperLink(String name, String url) {
    super(name);
    this.setOnAction(actionEvent -> HostServiceSingleton.getInstance().showDocument(url));
  }
}
