package edu.kit.iti.formal.stvs.view.menu;

import javafx.collections.ObservableList;
import javafx.scene.Node;
import javafx.stage.FileChooser;
import javafx.stage.Stage;

import java.io.File;
import java.util.Optional;

/**
 * Created by csicar on 30.01.17.
 * @author Carsten Csiky
 */
public class StvsFileChooserManager {
  private FileChooser fileChooser;
  private Optional<File> chosenFile;

  public StvsFileChooserManager(Stage stage, String title) {
    fileChooser = new FileChooser();
    fileChooser.setTitle(title);
    fileChooser.setInitialDirectory(
        new File(System.getProperty("user.home"))
    );
    chosenFile = Optional.ofNullable(fileChooser.showOpenDialog(stage));
  }

  public StvsFileChooserManager(Stage stage) {
    this(stage, "Open a file");
  }

  public StvsFileChooserManager(Node node) {
    //seems legit http://stackoverflow.com/a/31686775
    this((Stage) node.getScene().getWindow());
  }

  public Optional<File> getFile() {
    return this.chosenFile;
  }

  public ObservableList<FileChooser.ExtensionFilter> getExtensionFilters()  {
    return fileChooser.getExtensionFilters();
  }

}
