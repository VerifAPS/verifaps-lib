package edu.kit.iti.formal.stvs.view;

import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.ContextMenu;

/**
 * Created by csicar on 09.01.17.
 */
public class StvsMainScene extends Scene {
  private StvsRootController rootController;
  private ContextMenu contextMenu;

  public StvsMainScene(Parent root) {
    super(root);
  }

  public StvsRootController getRootController() {
    return rootController;
  }

  public void setRootController(StvsRootController rootController) {
    this.rootController = rootController;
  }
}
