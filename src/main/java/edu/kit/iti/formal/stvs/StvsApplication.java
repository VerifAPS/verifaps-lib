package edu.kit.iti.formal.stvs;

import edu.kit.iti.formal.stvs.view.StvsMainScene;
import javafx.application.Application;
import javafx.stage.Stage;

/**
 * Created by csicar on 09.01.17.
 */
public class StvsApplication extends Application {

  public static void main(String[] args) {
    launch(args);
  }

  @Override
  public void start(Stage primaryStage) {
    StvsMainScene mainScene = new StvsMainScene();
    primaryStage.setTitle("Structured Text Verification Studio - STVS");
    primaryStage.setScene(mainScene.getScene());
    primaryStage.setOnCloseRequest(event -> System.exit(0));
    primaryStage.setMaximized(true);
    primaryStage.show();
  }
}
