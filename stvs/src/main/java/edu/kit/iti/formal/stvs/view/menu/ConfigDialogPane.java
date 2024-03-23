package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.view.ViewUtils;
import edu.kit.iti.formal.stvs.view.common.FileSelectionField;
import edu.kit.iti.formal.stvs.view.common.PositiveIntegerInputField;
import javafx.geometry.Insets;
import javafx.scene.control.ButtonBar;
import javafx.scene.control.ButtonType;
import javafx.scene.control.CheckBox;
import javafx.scene.control.ComboBox;
import javafx.scene.control.DialogPane;
import javafx.scene.control.Label;
import javafx.scene.control.TextField;
import javafx.scene.layout.GridPane;
import javafx.scene.text.Text;

/**
 * <p>
 * The view for a config dialog. Includes numerous text fields, checkboxes and number text fields
 * that match the fields of a {@link edu.kit.iti.formal.stvs.model.config.GlobalConfig}.
 * </p>
 *
 * <p>
 * Created by csicar on 11.01.17.
 * </p>
 *
 * @author Carsten Csiky
 */
public class ConfigDialogPane extends DialogPane {
  public final FileSelectionField nuxmvFilename;
  public final FileSelectionField z3Path;
  public final TextField getetaCommand;
  public final PositiveIntegerInputField maxLineRollout;
  public final PositiveIntegerInputField verificationTimeout;
  public final PositiveIntegerInputField simulationTimeout;
  public final PositiveIntegerInputField editorFontSize;
  public final TextField editorFontFamily;
  public final CheckBox showLineNumbers;
  public final ComboBox<String> uiLanguage;
  public final ButtonType okButtonType;

  /**
   * <p>
   * Creates the view for a config dialog.
   * </p>
   *
   * <p>
   * Text fields and checkboxes have to be initialized from a
   * {@link edu.kit.iti.formal.stvs.model.config.GlobalConfig} model. For that, use the
   * {@link ConfigDialogManager}.
   * </p>
   */
  public ConfigDialogPane() {
    verificationTimeout = new PositiveIntegerInputField();
    simulationTimeout = new PositiveIntegerInputField();
    editorFontSize = new PositiveIntegerInputField();
    editorFontFamily = new TextField();
    showLineNumbers = new CheckBox();
    uiLanguage = new ComboBox<>();
    nuxmvFilename = new FileSelectionField();
    z3Path = new FileSelectionField();
    getetaCommand = new TextField();
    maxLineRollout = new PositiveIntegerInputField();
    okButtonType = new ButtonType("Save", ButtonBar.ButtonData.OK_DONE);


    this.getButtonTypes().addAll(okButtonType, ButtonType.CANCEL);


    GridPane grid = new GridPane();
    grid.setHgap(10);
    grid.setVgap(10);
    grid.setPadding(new Insets(20, 10, 10, 10));

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

    grid.add(new Label("GeTeTa Command"), 0, 9);
    grid.add(getetaCommand, 1, 9);
    Text getetaCommandDescription =
        new Text("Use ${code} and ${spec} for code and specification" + " filename substitution.");
    getetaCommandDescription.setStyle("-fx-font-style: italic");
    grid.add(getetaCommandDescription, 0, 10, 2, 1);

    grid.add(new Label("Maximum Number of Rollouts per Line"), 0, 11);
    grid.add(maxLineRollout, 1, 11);
    this.setContent(grid);
    ViewUtils.setupClass(this);

  }
}
