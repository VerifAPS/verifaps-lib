package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.ViewUtils;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.menu.StvsMenuBarController;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ObservableValue;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.ContextMenu;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;

/**
 * Created by csicar on 09.01.17.
 */
public class StvsMainScene {

  private static final String AUTOLOAD_CONFIG_FILENAME = "stvs-config.xml";
  private static final String CONFIG_DIRNAME = ".config";
  private StvsMenuBarController menuBarController;
  private StvsRootController rootController;
  private ObjectProperty<StvsRootModel> rootModelProperty;
  private ContextMenu contextMenu;
  private final Scene scene;

  public StvsMainScene() {
    this(new StvsRootModel());
  }

  public StvsMainScene(StvsRootModel rootModel) {
    this.rootModelProperty = new SimpleObjectProperty<>(rootModel);
    this.rootController = new StvsRootController(rootModelProperty.get());
    this.menuBarController = new StvsMenuBarController(rootModelProperty);

    this.rootModelProperty.get().getGlobalConfig().setAll(autoloadConfig());

    rootModelProperty.addListener(this::rootModelChanged);

    this.scene = new Scene(createVBox(), rootModel.getGlobalConfig().getWindowWidth(), rootModel.getGlobalConfig().getWindowHeight());
    rootModel.getGlobalConfig().windowWidthProperty().bind(scene.widthProperty());
    rootModel.getGlobalConfig().windowHeightProperty().bind(scene.heightProperty());
  }

  public static GlobalConfig autoloadConfig() {
    String userHome = System.getProperty("user.home");
    String configDirPath = userHome + File.separator + CONFIG_DIRNAME;
    File configFile = new File(configDirPath + File.separator + AUTOLOAD_CONFIG_FILENAME);
    try {
        return ImporterFacade.importConfig(configFile, ImporterFacade.ImportFormat.XML);
    } catch (Exception e) {
        return new GlobalConfig();
    }
  }

  public void autosaveConfig() {
    String userHome = System.getProperty("user.home");
    String configDirPath = userHome + File.separator + CONFIG_DIRNAME;
    File configDir = new File(configDirPath);
    if (!configDir.isDirectory() || !configDir.exists()) {
      configDir.mkdirs();
    }
    File configFile = new File(configDirPath + File.separator + AUTOLOAD_CONFIG_FILENAME);
    try {
      ExporterFacade.exportConfig(rootModelProperty.get().getGlobalConfig(), ExporterFacade
          .ExportFormat.XML, configFile);
    } catch (Exception e) {
      ViewUtils.showDialog(Alert.AlertType.ERROR, "Autosave Error", "Error saving the " +
          "configuration file", "The current configuration cannot be saved. Please check access " +
          "permissions for " + configDirPath + ".");
    }
  }

  private VBox createVBox() {
    VBox vBox = new VBox();
    vBox.getChildren().addAll(menuBarController.getView(), rootController.getView());
    VBox.setVgrow(rootController.getView(), Priority.ALWAYS);

    return vBox;
  }

  private void rootModelChanged(
      ObservableValue<? extends StvsRootModel> obs,
      StvsRootModel oldModel,
      StvsRootModel rootModel) {
    this.rootController = new StvsRootController(rootModel);
    scene.setRoot(createVBox());
  }

  public StvsRootController getRootController() {
    return rootController;
  }

  public void setRootController(StvsRootController rootController) {
    this.rootController = rootController;
  }

  public Scene getScene() {
    return scene;
  }
}
