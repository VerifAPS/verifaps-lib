package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.view.common.AlertFactory;
import edu.kit.iti.formal.stvs.view.menu.StvsMenuBarController;

import java.io.IOException;

import javafx.beans.property.BooleanProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ObservableValue;
import javafx.scene.Scene;
import javafx.scene.control.Alert;
import javafx.scene.control.ContextMenu;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

import javax.xml.bind.JAXBException;

/**
 * Main Scene that holds all visible nodes of the program.
 *
 * @author Lukas Fritsch
 */
public class StvsMainScene {

  private StvsMenuBarController menuBarController;
  private StvsRootController rootController;
  private ObjectProperty<StvsRootModel> rootModelProperty;
  private ContextMenu contextMenu;
  private final Scene scene;

  public StvsMainScene() {
    this(StvsRootModel.autoloadSession());
  }

  /**
   * Creates an instance from a root model.
   * @param rootModel Model that should be represented by this instance.
   */
  public StvsMainScene(StvsRootModel rootModel) {
    this.rootModelProperty = new SimpleObjectProperty<>(rootModel);
    this.rootController = new StvsRootController(rootModelProperty.get());
    this.menuBarController = new StvsMenuBarController(rootModelProperty);
    this.rootModelProperty.get().getGlobalConfig().setAll(GlobalConfig.autoloadConfig());
    this.rootModelProperty.get().getHistory().setAll(History.autoloadHistory());

    rootModelProperty.addListener(this::rootModelChanged);

    this.scene = new Scene(createVBox(), rootModel.getGlobalConfig().getWindowWidth(),
        rootModel.getGlobalConfig().getWindowHeight());

    rootModel.getGlobalConfig().windowWidthProperty().bind(scene.widthProperty());
    rootModel.getGlobalConfig().windowHeightProperty().bind(scene.heightProperty());
  }

  private VBox createVBox() {
    VBox vbox = new VBox();
    vbox.getChildren().addAll(menuBarController.getView(), rootController.getView());
    VBox.setVgrow(rootController.getView(), Priority.ALWAYS);

    return vbox;
  }

  private void rootModelChanged(ObservableValue<? extends StvsRootModel> obs,
      StvsRootModel oldModel, StvsRootModel rootModel) {
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

  /**
   * Code that should be executed before the scene is destroyed on exit.
   */
  public void onClose() {
    StvsRootModel stvsRootModel = rootModelProperty.get();
    if (stvsRootModel != null) {
      try {
        stvsRootModel.getGlobalConfig().autosaveConfig();
        stvsRootModel.getHistory().autosaveHistory();
        stvsRootModel.autosaveSession();
      } catch (IOException | ExportException | JAXBException e) {
        AlertFactory.createAlert(Alert.AlertType.ERROR, "Autosave error",
            "Error saving the current" + " configuration",
            "The current configuration could not be saved.", e.getMessage()).showAndWait();
      }
    }
  }

  public BooleanProperty shouldBeMaximizedProperty() {
    return rootModelProperty.get().getGlobalConfig().windowMaximizedProperty();
  }
}
