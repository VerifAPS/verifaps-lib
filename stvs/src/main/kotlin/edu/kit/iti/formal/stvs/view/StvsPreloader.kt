package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.StvsApplication;
import javafx.application.Platform;
import javafx.application.Preloader;
import javafx.geometry.Insets;
import javafx.geometry.Rectangle2D;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.control.ProgressBar;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.scene.layout.Background;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.Region;
import javafx.scene.layout.VBox;
import javafx.scene.paint.Color;
import javafx.stage.Screen;
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
  private Image splashImage;


  @Override
  public void init() {
    splashImage = new Image(StvsApplication.class.getResourceAsStream("logo.png"));
  }

  @Override
  public void start(Stage stage) {
    this.stage = stage;

    stage.initStyle(StageStyle.TRANSPARENT);

    VBox box = new VBox(20);
    box.setMaxWidth(Region.USE_PREF_SIZE);
    box.setMaxHeight(Region.USE_PREF_SIZE);
    box.setBackground(Background.EMPTY);
    String style = "-fx-background-color: rgba(255, 255, 255, 0.5);";
    box.setStyle(style);

    box.setPadding(new Insets(50));
    BorderPane root = new BorderPane(box);
    root.setStyle(style);
    root.setBackground(Background.EMPTY);
    Scene scene = new Scene(root);
    scene.setFill(Color.TRANSPARENT);
    stage.setScene(scene);

    ImageView splashView = new ImageView(splashImage);
    box.getChildren().addAll(splashView, new Label("ST Verification Studio is loading.."));
    stage.show();
    Rectangle2D primScreenBounds = Screen.getPrimary().getVisualBounds();
    stage.setX((primScreenBounds.getWidth() - stage.getWidth()) / 2);
    stage.setY((primScreenBounds.getHeight() - stage.getHeight()) / 2);
  }

  @Override
  public void handleStateChangeNotification(StateChangeNotification evt) {
    if (evt.getType() == StateChangeNotification.Type.BEFORE_START) {
      try {
        Thread.sleep(1000);
      } catch (InterruptedException e) {
        e.printStackTrace();
      }
      stage.hide();
    }
  }
}
