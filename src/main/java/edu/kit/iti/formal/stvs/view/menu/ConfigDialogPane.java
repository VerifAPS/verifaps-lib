package edu.kit.iti.formal.stvs.view.menu;

import javafx.geometry.Insets;
import javafx.scene.control.*;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.VBox;

import javax.xml.soap.Text;

/**
 * Created by csicar on 11.01.17.
 */
public class ConfigDialogPane extends DialogPane {
  public TextField verificationTimeout;
  public TextField simulationTimeout;
  public TextField windowHeight;
  public TextField windowWidth;
  public TextField editorFontSize;
  public TextField editorFontFamily;
  public CheckBox showLineNumbers;
  public ComboBox<String> uiLanguage;


  public ConfigDialogPane() {
    verificationTimeout = new TextField();
    simulationTimeout = new TextField();
    windowHeight = new TextField();
    windowWidth = new TextField();
    editorFontSize = new TextField();
    editorFontFamily = new TextField();
    showLineNumbers = new CheckBox();
    uiLanguage = new ComboBox<>();

    this.getButtonTypes().addAll( ButtonType.OK, ButtonType.CANCEL);


    GridPane grid = new GridPane();
    grid.setHgap(10);
    grid.setVgap(10);
    grid.setPadding(new Insets(20, 150, 10, 10));

    grid.add(verificationTimeout, 1, 0);
    grid.add(simulationTimeout, 1, 1);
    grid.add(windowHeight, 1, 2);
    grid.add(windowWidth, 1, 3);
    grid.add(editorFontSize, 1, 4);
    grid.add(editorFontFamily, 1, 5);
    grid.add(showLineNumbers, 1, 6);
    grid.add(uiLanguage, 1, 7);

    this.setContent(grid);
  }
}
