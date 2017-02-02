package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.binding.Bindings;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.IntegerProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.scene.Scene;
import javafx.scene.control.ButtonType;
import javafx.scene.control.Dialog;
import javafx.stage.Stage;
import javafx.util.converter.NumberStringConverter;

/**
 * Created by csicar on 11.01.17.
 */
public class ConfigDialogManager implements Controller {
  private GlobalConfig config;
  private Stage stage;
  private Scene scene;
  private ConfigDialogPane view;

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

  public ConfigDialogManager(GlobalConfig config) {
    this.config = config;
    this.view = new ConfigDialogPane();
    this.stage = new Stage();
    Dialog<GlobalConfig> dialog = new Dialog<>();
    dialog.setTitle("Configuration");
    view = new ConfigDialogPane();
    //set initial values
    view.uiLanguage.setItems(FXCollections.observableList(config.getValidLanguages()));
    bind(view.verificationTimeout.textProperty(), config.verificationTimeoutProperty());
    bind(view.simulationTimeout.textProperty(),   config.simulationTimeoutProperty());
    bind(view.windowHeight.textProperty(),        config.windowHeightProperty());
    bind(view.windowWidth.textProperty(),         config.windowWidthProperty());
    bind(view.editorFontFamily.textProperty(),    config.editorFontFamilyProperty());
    bind(view.editorFontSize.textProperty(),      config.editorFontSizeProperty());
    bind(view.showLineNumbers.selectedProperty(), config.showLineNumbersProperty());
    bind(view.uiLanguage.valueProperty(),         config.uiLanguageProperty());

    dialog.setDialogPane(view);
    dialog.setResultConverter(buttonType -> {
      if (buttonType != ButtonType.OK) {
        return null;
      }
      config.setEditorFontFamily(view.editorFontFamily.getText());
      config.setEditorFontSize(Integer.valueOf(view.editorFontSize.getText()));
      config.setShowLineNumbers(view.showLineNumbers.isSelected());
      config.setSimulationTimeout(Integer.valueOf(view.simulationTimeout.getText()));
      config.setVerificationTimeout(Integer.valueOf(view.verificationTimeout.getText()));
      config.setUiLanguage(view.uiLanguage.valueProperty().get());
      config.setWindowHeight(Integer.valueOf(view.windowHeight.getText()));
      config.setWindowWidth(Integer.valueOf(view.windowWidth.getText()));
      return config;
    });
    dialog.showAndWait();
  }



  @Override
  public ConfigDialogPane getView() {
    return view;
  }
}
