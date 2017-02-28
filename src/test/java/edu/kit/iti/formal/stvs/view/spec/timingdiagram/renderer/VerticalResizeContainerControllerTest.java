package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.view.JavaFxTest;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.layout.Pane;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;
import javafx.scene.paint.Color;
import javafx.scene.shape.Rectangle;
import org.junit.Test;

/**
 * Created by leonk on 10.02.2017.
 */
public class VerticalResizeContainerControllerTest {

  @Test
  public void javaFxTest() {
    JavaFxTest.setToBeViewed(this::simpleScene);
    Application.launch(JavaFxTest.class);
  }

  private Scene simpleScene() {
    try {
      VBox root = new VBox();
      Pane pane = new Pane();
      Rectangle rectangle = new Rectangle(100, 100, Color.AQUA);
      pane.getChildren().addAll(rectangle);
      VerticalResizeContainerController controller = new VerticalResizeContainerController(pane);
      root.getChildren().addAll(controller.getView());
      VBox.setVgrow(controller.getView(), Priority.ALWAYS);
      Scene scene = new Scene(root, 800, 600);
      return scene;
    } catch (Exception e) {
      e.printStackTrace();
      return null;
    }
  }

}