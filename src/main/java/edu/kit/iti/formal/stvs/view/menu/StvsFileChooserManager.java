package edu.kit.iti.formal.stvs.view.menu;

import javafx.stage.FileChooser;
import javafx.stage.Stage;

import java.io.File;

/**
 * Created by csicar on 30.01.17.
 */
public class StvsFileChooserManager {
  private FileChooser fileChooser;

  public StvsFileChooserManager(Stage stage) {
    fileChooser = new FileChooser();
    fileChooser.setTitle("Open a File");
    fileChooser.showOpenDialog(stage);
    fileChooser.setInitialDirectory(
        new File(System.getProperty("user.home"))
    );
  }
}
