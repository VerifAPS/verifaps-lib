package edu.kit.iti.formal.stvs;
/**
 * Created by csicar on 09.01.17.
 */

import edu.kit.iti.formal.stvs.view.StvsMainScene;
import edu.kit.iti.formal.stvs.view.StvsRootView;
import javafx.application.Application;
import javafx.scene.Scene;
import javafx.stage.Stage;

public class StvsApplication extends Application {

  public static void main(String[] args) {
    launch(args);
  }

  @Override
  public void start(Stage primaryStage) {
    StvsMainScene mainScene = new StvsMainScene();
    primaryStage.setTitle("Structured Text Verification Studio - STVS");
    primaryStage.setScene(mainScene.getScene());
    primaryStage.show();
  }
}
