package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.view.common.FileSelectionField;
import javafx.geometry.Insets;
import javafx.scene.control.*;
import javafx.scene.layout.GridPane;

/**
 * Created by csicar on 11.01.17.
 */
public class ConfigDialogPane extends DialogPane {
  public final FileSelectionField nuxmvFilename;
  public final FileSelectionField z3Path;
  public final FileSelectionField javaPath;
  public final FileSelectionField getetaFilename;
  public final TextField maxLineRollout;
  public final TextField verificationTimeout;
  public final TextField simulationTimeout;
  public final TextField windowHeight;
  public final TextField windowWidth;
  public final TextField editorFontSize;
  public final TextField editorFontFamily;
  public final CheckBox showLineNumbers;
  public final ComboBox<String> uiLanguage;


  public ConfigDialogPane() {
    verificationTimeout = new TextField();
    simulationTimeout = new TextField();
    windowHeight = new TextField();
    windowWidth = new TextField();
    editorFontSize = new TextField();
    editorFontFamily = new TextField();
    showLineNumbers = new CheckBox();
    uiLanguage = new ComboBox<>();
    nuxmvFilename = new FileSelectionField();
    z3Path = new FileSelectionField();
    javaPath = new FileSelectionField();
    getetaFilename = new FileSelectionField();
    maxLineRollout = new TextField();


    this.getButtonTypes().addAll( ButtonType.OK, ButtonType.CANCEL);


    GridPane grid = new GridPane();
    grid.setHgap(10);
    grid.setVgap(10);
    grid.setPadding(new Insets(20, 150, 10, 10));

    grid.add(new Label("Verification Timeout"), 0, 0);
    grid.add(verificationTimeout, 1, 0);

    grid.add(new Label("Simulation Timeout"), 0, 1);
    grid.add(simulationTimeout, 1, 1);

    grid.add(new Label("Window Height"), 0, 2);
    grid.add(windowHeight, 1, 2);

    grid.add(new Label("Window Width"), 0, 3);
    grid.add(windowWidth, 1, 3);

    grid.add(new Label("Editor Fontsize"), 0, 4);
    grid.add(editorFontSize, 1, 4);

    grid.add(new Label("Editor Font Family"), 0, 5);
    grid.add(editorFontFamily, 1, 5);

    grid.add(new Label("Show Line Numbers"), 0, 6);
    grid.add(showLineNumbers, 1, 6);

    grid.add(new Label("User Interface Language"), 0, 7);
    grid.add(uiLanguage, 1, 7);


    grid.add(new Label("Path to NuXmv Executable"), 0, 8);
    grid.add(nuxmvFilename, 1, 8);


    grid.add(new Label("Path to Z3"), 0, 9);
    grid.add(z3Path, 1, 9);


    grid.add(new Label("Path to Java"), 0, 10);
    grid.add(javaPath, 1, 10);


    grid.add(new Label("Path to GeTeTa"), 0, 11);
    grid.add(getetaFilename, 1, 11);


    grid.add(new Label("Maximum Number of Rollouts per Line"), 0, 12);
    grid.add(maxLineRollout, 1, 12);
    this.setContent(grid);
  }
}
