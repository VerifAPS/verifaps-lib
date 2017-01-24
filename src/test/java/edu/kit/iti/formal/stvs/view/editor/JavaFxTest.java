package edu.kit.iti.formal.stvs.view.editor;

import javafx.application.Application;
import javafx.scene.Scene;
import javafx.scene.layout.Pane;
import javafx.stage.Stage;

import java.util.Collections;
import java.util.function.Supplier;

/**
 * Created by Lukas on 20.01.2017.
 */
public class JavaFxTest extends Application {

  private static Supplier<Scene> toBeViewed;

  public static void main(String[] args) {
    launch(args);
  }

  public static void setToBeViewed(Supplier<Scene> toBeViewed) {
    JavaFxTest.toBeViewed = toBeViewed;
  }

  @Override
  public void start(Stage primaryStage) throws Exception {
    primaryStage.setScene(toBeViewed.get());
    primaryStage.show();
  }
}
