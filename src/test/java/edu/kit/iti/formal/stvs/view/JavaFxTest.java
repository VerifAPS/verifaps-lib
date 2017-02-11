package edu.kit.iti.formal.stvs.view;

import javafx.application.Application;
import javafx.geometry.Orientation;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.SplitPane;
import javafx.stage.Stage;

import java.util.List;
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

  public static void runView(Supplier<Scene> toBeViewed) {
    setToBeViewed(toBeViewed);
    Application.launch(JavaFxTest.class);
  }

  public static void runSplitView(Supplier<List<Node>> supplierOfViews) {
    runView(() -> {
      SplitPane pane = new SplitPane();
      pane.getItems().addAll(supplierOfViews.get());

      Scene scene = new Scene(pane, 800, 600);

      scene.getStylesheets().add(JavaFxTest.class.getResource("style.css").toExternalForm());

      return scene;
    });
  }

  @Override
  public void start(Stage primaryStage) throws Exception {
    primaryStage.setScene(toBeViewed.get());
    primaryStage.show();
  }
}
