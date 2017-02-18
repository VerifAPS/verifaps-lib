package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.view.Controller;
import javafx.application.Platform;
import javafx.beans.property.DoubleProperty;
import javafx.beans.property.SimpleDoubleProperty;
import javafx.scene.Node;
import javafx.scene.layout.AnchorPane;

/**
 * Controller for {@link VerticalResizeContainerView}
 *
 * @author Leon Kaucher
 */
public class VerticalResizeContainerController implements Controller {
  VerticalResizeContainerView view = new VerticalResizeContainerView();
  private DoubleProperty mouseYStart = new SimpleDoubleProperty(0);
  private DoubleProperty cacheSize = new SimpleDoubleProperty(0);

  /**
   * Creates a simple wrapper that enables one to vertically resize the given Node.
   *
   * @param wrap Node that should be wrapped
   */
  public VerticalResizeContainerController(Node wrap) {
    view.getContent().getChildren().add(wrap);
    AnchorPane.setLeftAnchor(wrap, 0.0);
    AnchorPane.setRightAnchor(wrap, 0.0);
    AnchorPane.setTopAnchor(wrap, 0.0);
    AnchorPane.setBottomAnchor(wrap, 0.0);
    view.getDragLine().setOnMousePressed(event -> {
      mouseYStart.setValue(event.getScreenY());
      cacheSize.setValue(view.getContent().getHeight());
      view.getContentContainer().setPrefHeight(view.getContent().getHeight());
    });
    view.getDragLine().setOnMouseDragged(event -> {
      double newSize = cacheSize.get() + (event.getScreenY() - mouseYStart.get());
      if (newSize >= cacheSize.get()) {
        view.getContentContainer().setPrefHeight(newSize);
      }
      view.getContent().setPrefHeight(newSize);
    });
    view.getDragLine().setOnMouseReleased(event -> {
      System.out.println("release");
      double newSize = cacheSize.get() + (event.getScreenY() - mouseYStart.get());
      view.getContentContainer().setPrefHeight(newSize);
      view.getContent().setPrefHeight(newSize);
      Platform.runLater(() -> view.getParent().getParent().getParent().getParent().getParent().getParent().requestLayout());
    });
  }

  @Override
  public Node getView() {
    return view;
  }
}
