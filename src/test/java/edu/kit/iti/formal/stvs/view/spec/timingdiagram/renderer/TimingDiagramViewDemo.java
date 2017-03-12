package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.Demo;
import edu.kit.iti.formal.stvs.view.JavaFxTest;
import javafx.scene.Scene;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.experimental.categories.Category;

/**
 * Created by leonk on 02.02.2017.
 */
@Category(Demo.class)
public class TimingDiagramViewDemo {
  @Ignore
  @Test
  public void javaFxTest() {
    JavaFxTest.runView(this::simpleScene);
  }

  private Scene simpleScene() {
    /*TimingDiagramController controller = new TimingDiagramController(new NumberAxis(),new NumberAxis());
    Pane pane = new Pane();
    pane.getChildren().add(controller.getView());
    Scene scene = new Scene(pane, 800, 600);
    //scene.getStylesheets().add(this.getClass().getResource("style.css").toExternalForm());
    return scene;*/
    return null;
  }
}