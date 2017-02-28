package edu.kit.iti.formal.stvs;

import edu.kit.iti.formal.stvs.view.StvsMainScene;
import javafx.application.Application;
import javafx.application.Platform;
import javafx.scene.image.Image;
import javafx.stage.Stage;

/**
 * Created by csicar on 09.01.17.
 *
 * @author Benjamin Alt
 */
public class StvsApplication extends Application {

  private StvsMainScene mainScene = new StvsMainScene();

  public static void main(String[] args) {
    launch(args);
  }

  @Override
  public void start(Stage primaryStage) {
    Platform.setImplicitExit(true);
    mainScene = new StvsMainScene();
    primaryStage.setTitle("Structured Text Verification Studio - STVS");
    primaryStage.setScene(mainScene.getScene());
    primaryStage.setMaximized(mainScene.shouldBeMaximizedProperty().get());
    mainScene.shouldBeMaximizedProperty().bind(primaryStage.maximizedProperty());
    primaryStage.getIcons().add(new Image(StvsApplication.class
        .getResourceAsStream("clipboard.png")));
    primaryStage.show();
  }

  @Override
  public void stop() {
    mainScene.onClose();
    System.exit(0);
  }
}
