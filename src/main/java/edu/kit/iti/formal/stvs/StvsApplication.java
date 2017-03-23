package edu.kit.iti.formal.stvs;

import edu.kit.iti.formal.stvs.view.StvsMainScene;
import edu.kit.iti.formal.stvs.view.common.HostServiceSingleton;
import edu.kit.iti.formal.stvs.view.menu.WelcomeWizard;
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
  private Stage primaryStage;

  /**
   * Launch the application.
   * 
   * @param args The command-line arguments passed to the application
   */
  public static void main(String[] args) {
    launch(args);
  }

  @Override
  public void init() {
    HostServiceSingleton.setInstance(getHostServices());
    this.mainScene = new StvsMainScene();

    Platform.runLater(() -> {
      this.primaryStage = new Stage();
      Platform.setImplicitExit(true);
      primaryStage.setTitle("Structured Text Verification Studio - STVS");
      primaryStage.setScene(mainScene.getScene());
      primaryStage.setMaximized(mainScene.shouldBeMaximizedProperty().get());
      primaryStage.getIcons().addAll(
          new Image(StvsApplication.class.getResourceAsStream("logo_large.png")),
          new Image(StvsApplication.class.getResourceAsStream("logo.png")));
      mainScene.shouldBeMaximizedProperty().bind(primaryStage.maximizedProperty());

      if(mainScene.getRootController().getRootModel().isFirstStart()) {
        new WelcomeWizard(mainScene.getRootController().getRootModel().getGlobalConfig())
            .showAndWait();
      }

      primaryStage.show();

    });
  }

  @Override
  public void start(Stage primaryStage) {
    primaryStage.hide();
  }

  @Override
  public void stop() {
    mainScene.onClose();
    this.primaryStage.hide();
    System.exit(0);
  }
}
