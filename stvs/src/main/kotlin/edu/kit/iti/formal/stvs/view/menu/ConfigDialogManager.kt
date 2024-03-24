package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.common.AlertFactory;

import java.io.IOException;

import javafx.beans.binding.BooleanBinding;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.IntegerProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Dialog;
import javafx.stage.Stage;

/**
 * <p>
 * The manager for the Config dialog view (with its model being the {@link GlobalConfig}).
 * </p>
 *
 * <p>
 * Created by csicar on 11.01.17.
 * </p>
 *
 * @author Carsten Csiky
 */
public class ConfigDialogManager implements Controller {
  private GlobalConfig config;
  private ConfigDialogPane view;
  private Dialog<GlobalConfig> dialog;
  private BooleanBinding dialogValid;

  /**
   * <p>
   * Creates the manager for the config dialog view. Here the model is bound to the view.
   * </p>
   *
   * @param config the model to bind to the view
   */
  public ConfigDialogManager(GlobalConfig config) {
    this.config = config;
    this.view = new ConfigDialogPane();
    dialog = new Dialog<>();
    dialog.setTitle("Preferences");
    view = new ConfigDialogPane();
    // set initial values
    view.uiLanguage.setItems(FXCollections.observableList(config.getValidLanguages()));
    bind(view.verificationTimeout.textProperty(), config.verificationTimeoutProperty());
    bind(view.simulationTimeout.textProperty(), config.simulationTimeoutProperty());
    bind(view.editorFontFamily.textProperty(), config.editorFontFamilyProperty());
    bind(view.editorFontSize.textProperty(), config.editorFontSizeProperty());
    bind(view.showLineNumbers.selectedProperty(), config.showLineNumbersProperty());
    bind(view.uiLanguage.valueProperty(), config.uiLanguageProperty());
    bind(view.maxLineRollout.textProperty(), config.maxLineRolloutProperty());
    bind(view.nuxmvFilename.getTextField().textProperty(), config.nuxmvFilenameProperty());
    bind(view.z3Path.getTextField().textProperty(), config.z3PathProperty());
    bind(view.getetaCommand.textProperty(), config.getetaCommandProperty());

    dialogValid =
        view.verificationTimeout.validProperty().and(view.simulationTimeout.validProperty())
            .and(view.editorFontSize.validProperty()).and(view.maxLineRollout.validProperty());

    Node button = view.lookupButton(view.okButtonType);
    button.disableProperty().bind(dialogValid.not());

    dialog.setDialogPane(view);
    dialog.setResultConverter(this::convertResult);
  }

  private GlobalConfig convertResult(ButtonType buttonType) {
    if (buttonType != view.okButtonType) {
      return null;
    }
    if (!dialogValid.get()) {
      return null;
    }
    config.setEditorFontFamily(view.editorFontFamily.getText());
    config.setEditorFontSize(view.editorFontSize.getInteger().get());
    config.setShowLineNumbers(view.showLineNumbers.isSelected());
    config.setSimulationTimeout(view.simulationTimeout.getInteger().get());
    config.setVerificationTimeout(view.verificationTimeout.getInteger().get());
    config.setUiLanguage(view.uiLanguage.valueProperty().get());
    config.setMaxLineRollout(view.maxLineRollout.getInteger().get());
    config.setNuxmvFilename(view.nuxmvFilename.getTextField().getText());
    config.setZ3Path(view.z3Path.getTextField().getText());
    config.setGetetaCommand(view.getetaCommand.getText());
    try {
      config.autosaveConfig();
    } catch (IOException | ExportException exception) {
      AlertFactory.createAlert(Alert.AlertType.ERROR, "Autosave error",
          "Error saving the current configuration",
          "The current configuration could not be saved.", exception.getMessage()).showAndWait();
    }
    return config;
  }

  public void showAndWait() {
    dialog.showAndWait();
  }

  private void bind(StringProperty stringProperty, IntegerProperty integerProperty) {
    stringProperty.set(integerProperty.getValue().toString());
  }

  private void bind(StringProperty stringProperty, StringProperty integerProperty) {
    stringProperty.set(integerProperty.get());
  }

  private void bind(BooleanProperty booleanProperty, BooleanProperty booleanProperty2) {
    booleanProperty.set(booleanProperty2.get());
  }

  private void bind(ObjectProperty<String> objectProperty, StringProperty stringProperty) {
    objectProperty.set(stringProperty.get());
  }


  @Override
  public ConfigDialogPane getView() {
    return view;
  }
}
