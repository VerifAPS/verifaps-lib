package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.Demo;
import edu.kit.iti.formal.stvs.view.JavaFxTest;
import javafx.application.Application;
import javafx.beans.property.SimpleObjectProperty;
import javafx.scene.Scene;
import javafx.scene.layout.VBox;
import org.junit.Test;
import org.junit.experimental.categories.Category;

/**
 * Created by csicar on 30.01.17.
 */
@Category(Demo.class)
public class StvsMenuBarDemo {

  @Test
  public void javaFxTest() {
    JavaFxTest.setToBeViewed(this::simpleScene);
    Application.launch(JavaFxTest.class);
  }

  private Scene simpleScene() {
    Scene scene = new Scene(new VBox(), 400, 350);

    StvsRootModel rootModel = new StvsRootModel();

    StvsMenuBarController menuBarController = new StvsMenuBarController(new
        SimpleObjectProperty<>(rootModel));
    ((VBox) scene.getRoot()).getChildren().addAll(menuBarController.getView());

    return scene;
  }
}
