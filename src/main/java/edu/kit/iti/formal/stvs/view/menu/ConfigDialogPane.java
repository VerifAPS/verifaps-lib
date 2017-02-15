package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.view.common.FileSelectionField;
import edu.kit.iti.formal.stvs.view.common.IntegerInputField;
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
  public final IntegerInputField maxLineRollout;
  public final IntegerInputField verificationTimeout;
  public final IntegerInputField simulationTimeout;
  public final IntegerInputField editorFontSize;
  public final TextField editorFontFamily;
  public final CheckBox showLineNumbers;
  public final ComboBox<String> uiLanguage;
  public final ButtonType okButtonType;

  public ConfigDialogPane() {
    verificationTimeout = new IntegerInputField();
    simulationTimeout = new IntegerInputField();
    editorFontSize = new IntegerInputField();
    editorFontFamily = new TextField();
    showLineNumbers = new CheckBox();
    uiLanguage = new ComboBox<>();
    nuxmvFilename = new FileSelectionField();
    z3Path = new FileSelectionField();
    javaPath = new FileSelectionField();
    getetaFilename = new FileSelectionField();
    maxLineRollout = new IntegerInputField();
    okButtonType = new ButtonType("Save", ButtonBar.ButtonData.OK_DONE);


    this.getButtonTypes().addAll( okButtonType,  ButtonType.CANCEL);


    GridPane grid = new GridPane();
    grid.setHgap(10);
    grid.setVgap(10);
    grid.setPadding(new Insets(20, 150, 10, 10));

    grid.add(new Label("Verification Timeout"), 0, 0);
    grid.add(verificationTimeout, 1, 0);

    grid.add(new Label("Simulation Timeout"), 0, 1);
    grid.add(simulationTimeout, 1, 1);

    grid.add(new Label("Editor Fontsize"), 0, 2);
    grid.add(editorFontSize, 1, 2);

    grid.add(new Label("Editor Font Family"), 0, 3);
    grid.add(editorFontFamily, 1, 3);

    grid.add(new Label("Show Line Numbers"), 0, 4);
    grid.add(showLineNumbers, 1, 4);

    grid.add(new Label("User Interface Language"), 0, 5);
    grid.add(uiLanguage, 1, 5);


    grid.add(new Label("Path to NuXmv Executable"), 0, 6);
    grid.add(nuxmvFilename, 1, 6);


    grid.add(new Label("Path to Z3"), 0, 7);
    grid.add(z3Path, 1, 7);


    grid.add(new Label("Path to Java"), 0, 8);
    grid.add(javaPath, 1, 8);


    grid.add(new Label("Path to GeTeTa"), 0, 9);
    grid.add(getetaFilename, 1, 9);


    grid.add(new Label("Maximum Number of Rollouts per Line"), 0, 10);
    grid.add(maxLineRollout, 1, 10);
    this.setContent(grid);
  }
}
