package edu.kit.iti.formal.stvs.view.menu;

import javafx.scene.control.ButtonType;
import javafx.scene.control.DialogPane;
import javafx.scene.control.Label;
import javafx.scene.layout.VBox;

/**
 * Created by csicar on 16.02.17.
 */
public class AboutDialogPane extends DialogPane {

  private VBox content;

  public AboutDialogPane() {

    this.content = new VBox(
        new Label("Structured Text Verification Studio - STVS"),
        new Label("Version: 1.0"));
    this.setContent(content);
    this.getButtonTypes().addAll(ButtonType.CLOSE);
  }
}
