package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.view.ViewUtils;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.VBox;
import javafx.scene.paint.Color;
import javafx.scene.shape.Rectangle;

/**
 * Creates a Container for resizing through a horizontal bar.
 *
 * @author Leon Kaucher
 */
public class VerticalResizeContainerView extends AnchorPane {
  private VBox container = new VBox();
  private AnchorPane content = new AnchorPane();
  private VBox contentContainer = new VBox();
  private Rectangle dragLine = new Rectangle(10, 5, Color.BEIGE);

  public VerticalResizeContainerView() {
    this.getChildren().add(container);
    container.getChildren().addAll(contentContainer);
    contentContainer.getChildren().addAll(content, dragLine);
    AnchorPane.setLeftAnchor(container, 0.0);
    AnchorPane.setRightAnchor(container, 0.0);
    AnchorPane.setTopAnchor(container, 0.0);
    dragLine.widthProperty().bind(container.widthProperty());
    // AnchorPane.setBottomAnchor(dragLine, 0.0);
    ViewUtils.setupView(this, "resizeContainer.css");

    this.getStyleClass().add("resizeContainer");
    dragLine.getStyleClass().add("dragLine");
  }

  public VBox getContainer() {
    return container;
  }

  public AnchorPane getContent() {
    return content;
  }

  public VBox getContentContainer() {
    return contentContainer;
  }

  public Rectangle getDragLine() {
    return dragLine;
  }
}
