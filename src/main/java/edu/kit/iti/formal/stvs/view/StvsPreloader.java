package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.StvsApplication;
import javafx.application.Platform;
import javafx.application.Preloader;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.control.ProgressBar;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.scene.layout.Background;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Region;
import javafx.scene.layout.VBox;
import javafx.stage.Stage;
import javafx.stage.StageStyle;

import java.util.Calendar;
import java.util.Date;
import java.util.Timer;

/**
 * Created by csicar on 21.03.17.
 */
public class StvsPreloader extends Preloader {
  private Stage stage;


  @Override
  public void init() {
  }

  @Override
  public void start(Stage stage) {
    this.stage = stage;
    VBox box = new VBox(20);
    box.setMaxWidth(Region.USE_PREF_SIZE);
    box.setMaxHeight(Region.USE_PREF_SIZE);
    box.setBackground(Background.EMPTY);

    BorderPane root = new BorderPane(box);
    Scene scene = new Scene(root);
    scene.setFill(null);

    stage.setWidth(800);
    stage.setHeight(600);
    stage.initStyle(StageStyle.TRANSPARENT);
    stage.setScene(scene);


    stage.show();
    Platform.runLater(() -> {
      Image splashImage = new Image(StvsApplication.class.getResourceAsStream("logo_large.png"));
      ImageView splashView = new ImageView(splashImage);
      box.getChildren().addAll(splashView);
    });
  }

  @Override
  public void handleStateChangeNotification(StateChangeNotification evt) {
    if (evt.getType() == StateChangeNotification.Type.BEFORE_START) {

      stage.hide();
    }
  }
}
