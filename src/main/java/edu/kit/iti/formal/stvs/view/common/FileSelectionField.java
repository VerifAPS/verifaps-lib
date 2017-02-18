package edu.kit.iti.formal.stvs.view.common;

import edu.kit.iti.formal.stvs.view.menu.ConfigDialogPane;
import javafx.scene.control.TextField;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;
import javafx.stage.FileChooser;

import java.io.File;

/**
 * Created by csicar on 13.02.17.
 */
public class FileSelectionField extends TextField {
  public FileSelectionField() {
    super();
    setOnMousePressed(this::onMousePressed);
  }

  private void onMousePressed(MouseEvent mouseEvent) {
    FileChooser fileChooser = new FileChooser();
    fileChooser.setTitle("Select Executable");
    File selectedFile = fileChooser.showOpenDialog(this.getScene().getWindow());
    if (selectedFile != null) {
      setText(selectedFile.getAbsolutePath());
    }
  }
}
