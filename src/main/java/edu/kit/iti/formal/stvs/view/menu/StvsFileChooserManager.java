package edu.kit.iti.formal.stvs.view.menu;

import javafx.event.ActionEvent;
import javafx.event.EventDispatchChain;
import javafx.event.EventHandler;
import javafx.event.EventTarget;
import javafx.stage.FileChooser;
import javafx.stage.Stage;

import java.io.File;
import java.util.Optional;

/**
 * Created by csicar on 30.01.17.
 */
public class StvsFileChooserManager {
  private FileChooser fileChooser;
  private Optional<File> chosenFile;

  public StvsFileChooserManager(Stage stage) {
    fileChooser = new FileChooser();
    fileChooser.setTitle("Open a File");
    fileChooser.setInitialDirectory(
        new File(System.getProperty("user.home"))
    );
    chosenFile = Optional.ofNullable(fileChooser.showOpenDialog(stage));

  }

  public Optional<File> getFile() {
    return this.chosenFile;
  }


}
