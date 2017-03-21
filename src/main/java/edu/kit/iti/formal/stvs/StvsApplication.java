package edu.kit.iti.formal.stvs;

import edu.kit.iti.formal.stvs.view.StvsMainScene;
import javafx.application.Application;
import javafx.application.Platform;
import javafx.scene.image.Image;
import javafx.stage.Stage;

/**
 * The entry point to ST Verification Studio.
 *
 * @author Leon Kaucher
 */
public class StvsApplication extends Application {

  private StvsMainScene mainScene = new StvsMainScene();

  /**
   * Launch the application.
   * @param args The command-line arguments passed to the application
   */
  public static void main(String[] args) {
    launch(args);
  }

  @Override
  public void init() {
    Stage primaryStage = new Stage();
    this.mainScene = new StvsMainScene();
    Platform.setImplicitExit(true);
    primaryStage.setTitle("Structured Text Verification Studio - STVS");
    primaryStage.setScene(mainScene.getScene());
    primaryStage.setMaximized(mainScene.shouldBeMaximizedProperty().get());
    primaryStage.getIcons().addAll(
        new Image(StvsApplication.class.getResourceAsStream("logo_large.png")),
        new Image(StvsApplication.class.getResourceAsStream("logo.png")));
    primaryStage.show();

    mainScene.shouldBeMaximizedProperty().bind(primaryStage.maximizedProperty());
  }

  @Override
  public void start(Stage primaryStage) {
    primaryStage.show();
    primaryStage.hide();
  }

  @Override
  public void stop() {
    mainScene.onClose();
    System.exit(0);
  }
}
