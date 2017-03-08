package edu.kit.iti.formal.stvs.view.menu;

import static edu.kit.iti.formal.stvs.view.common.FileChooserFactory.FileType.ANY;
import static edu.kit.iti.formal.stvs.view.common.FileChooserFactory.FileType.CODE;
import static edu.kit.iti.formal.stvs.view.common.FileChooserFactory.FileType.SESSION;
import static edu.kit.iti.formal.stvs.view.common.FileChooserFactory.FileType.SPECIFICATION;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.ParsedCode;
import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.common.AlertFactory;
import edu.kit.iti.formal.stvs.view.common.FileChooserFactory;

import java.io.File;
import java.io.IOException;

import javafx.beans.property.ObjectProperty;
import javafx.event.ActionEvent;
import javafx.scene.control.Alert;
import javafx.scene.control.Dialog;
import javafx.scene.control.MenuItem;
import javafx.stage.FileChooser;


/**
 * Created by csicar on 10.01.17. Controller for the MenuBar at the top of the window does just fire
 * to the root controller
 *
 * @author Carsten Csiky
 */
public class StvsMenuBarController implements Controller {
  private StvsMenuBar view;
  private ObjectProperty<StvsRootModel> rootModel;

  /**
   * create a StvsMenuBarController; the parameters will be modified.
   *
   * @param rootModel the applications root model
   */
  public StvsMenuBarController(ObjectProperty<StvsRootModel> rootModel) {
    // set own properties
    this.rootModel = rootModel;

    // create view
    this.view = new StvsMenuBar();

    rootModel.get().getHistory().getFilenames().addListener(new HistoryFilenamesChangeListener());
    // Fill history menu
    updateHistoryMenu();

    // add listener
    view.newCode.setOnAction(this::createNewCode);
    view.newSpec.setOnAction(this::createNewSpec);
    view.open.setOnAction(this::openFile);
    view.openSession.setOnAction(this::openSession);
    view.openCode.setOnAction(this::openCode);
    view.openSpec.setOnAction(this::openSpec);
    view.saveAll.setOnAction(this::saveAll);
    view.saveSessionAs.setOnAction(this::saveSessionAs);
    view.saveCode.setOnAction(this::saveCode);
    view.saveSpec.setOnAction(this::saveSpec);
    view.config.setOnAction(this::openConfigDialog);
    view.about.setOnAction(this::openAboutDialog);
  }

  private void updateHistoryMenu() {
    view.openRecentItems.clear();
    for (String filename : rootModel.get().getHistory().getFilenames()) {
      MenuItem newItem = new MenuItem(filename);
      newItem.setOnAction((actionEvent -> {
        try {
          ImporterFacade.importFile(new File(filename), rootModel.get().getGlobalConfig(),
              rootModel.get().getHistory(), (hybridSpecification) -> {
                // handle hybridspecification
                rootModel.get().getHybridSpecifications().add(hybridSpecification);
              }, (rootModel) -> {
                // handle rootModel
                this.rootModel.setValue(rootModel);
              }, (code -> {
                // handle code
                this.rootModel.get().getScenario().setCode(code);
              }));
          this.rootModel.get().getHistory().addFilename(filename);
        } catch (IOException | ImportException e) {
          AlertFactory.createAlert(Alert.AlertType.ERROR, "File Open Error",
              "An error occurred " + "while opening a file.",
              "The file " + filename + " could not be opened.", e.getMessage()).showAndWait();
        }
      }));
      view.openRecentItems.add(newItem);
    }
    view.openRecent.getItems().clear();
    view.openRecent.getItems().addAll(view.openRecentItems);
  }

  private void saveSessionAs(ActionEvent actionEvent) {
    FileChooser fileChooser =
        FileChooserFactory.createSaveFileChooser(SESSION, rootModel.get().getWorkingdir());
    File chosenFile = fileChooser.showSaveDialog(view.getScene().getWindow());
    if (chosenFile != null) {
      handleSaveAll(chosenFile);
      if (chosenFile.isDirectory()) {
        rootModel.get().setWorkingdir(chosenFile);
      } else {
        rootModel.get().setWorkingdir(chosenFile.getParentFile());
      }
    }
  }

  private void createNewSpec(ActionEvent actionEvent) {
    rootModel.get().addNewHybridSpec();
  }

  private void createNewCode(ActionEvent actionEvent) {
    this.rootModel.get().getScenario().setCode(new Code());
  }

  private void openConfigDialog(ActionEvent t) {
    ConfigDialogManager dialogManager = new ConfigDialogManager(rootModel.get().getGlobalConfig());
  }

  private void openAboutDialog(ActionEvent actionEvent) {
    Dialog dialog = new Dialog();
    AboutDialogPane pane = new AboutDialogPane();
    dialog.setTitle("About");
    dialog.setDialogPane(pane);

    dialog.showAndWait();
  }

  private void openCode(ActionEvent t) {
    FileChooser fileChooser =
        FileChooserFactory.createOpenFileChooser(CODE, rootModel.get().getWorkingdir());
    File chosenFile = fileChooser.showOpenDialog(view.getScene().getWindow());
    if (chosenFile == null) {
      return;
    }
    try {
      Code code = ImporterFacade.importStCode(chosenFile);
      this.rootModel.get().getScenario().setCode(code);
      this.rootModel.get().getHistory().addFilename(chosenFile.getAbsolutePath());
    } catch (IOException e) {
      AlertFactory.createAlert(e).showAndWait();
    }
  }

  private void openSession(ActionEvent t) {
    FileChooser fileChooser =
        FileChooserFactory.createOpenFileChooser(SESSION, rootModel.get().getWorkingdir());
    File chosenFile = fileChooser.showOpenDialog(view.getScene().getWindow());

    if (chosenFile == null) {
      return;
    }
    try {
      StvsRootModel model =
          ImporterFacade.importSession(chosenFile, ImporterFacade.ImportFormat.XML,
              rootModel.get().getGlobalConfig(), rootModel.get().getHistory());
      model.setWorkingdir(chosenFile.getParentFile());
      model.setFilename(chosenFile.getName());
      this.rootModel.set(model);
      this.rootModel.get().getHistory().addFilename(chosenFile.getAbsolutePath());
    } catch (IOException | ImportException exception) {
      AlertFactory.createAlert(exception).showAndWait();
    }
  }

  private void openSpec(ActionEvent t) {
    FileChooser fileChooser =
        FileChooserFactory.createOpenFileChooser(SPECIFICATION, rootModel.get().getWorkingdir());
    File chosenFile = fileChooser.showOpenDialog(view.getScene().getWindow());
    if (chosenFile == null) {
      return;
    }
    try {
      HybridSpecification spec =
          ImporterFacade.importHybridSpec(chosenFile, ImporterFacade.ImportFormat.XML);
      this.rootModel.get().getHybridSpecifications().add(spec);
      this.rootModel.get().getHistory().addFilename(chosenFile.getAbsolutePath());
    } catch (IOException | ImportException e) {
      AlertFactory.createAlert(e).showAndWait();
    }
  }

  private void openFile(ActionEvent t) {
    FileChooser fileChooser =
        FileChooserFactory.createOpenFileChooser(ANY, rootModel.get().getWorkingdir());
    File chosenFile = fileChooser.showOpenDialog(view.getScene().getWindow());

    if (chosenFile == null) {
      return;
    }
    try {
      ImporterFacade.importFile(chosenFile, rootModel.get().getGlobalConfig(),
          rootModel.get().getHistory(), (hybridSpecification) -> {
            // handle hybridspecification
            rootModel.get().getHybridSpecifications().add(hybridSpecification);
          }, (rootModel) -> {
            // handle rootModel
            rootModel.setWorkingdir(chosenFile.getParentFile());
            rootModel.setFilename(chosenFile.getName());
            this.rootModel.setValue(rootModel);
          }, (code -> {
            // handle code
            this.rootModel.get().getScenario().setCode(code);
          }));
    } catch (IOException | ImportException e) {
      AlertFactory.createAlert(e).showAndWait();
    }
  }


  private void saveAll(ActionEvent t) {
    if (this.rootModel.get().getFilename().isEmpty()) {
      FileChooser fileChooser =
          FileChooserFactory.createSaveFileChooser(SESSION, rootModel.get().getWorkingdir());
      File chosenFile = fileChooser.showSaveDialog(view.getScene().getWindow());
      if (chosenFile != null) {
        handleSaveAll(chosenFile);
      }
    } else {
      handleSaveAll(new File(rootModel.get().getWorkingdir(), rootModel.get().getFilename()));
    }
  }

  private void handleSaveAll(File path) {
    try {
      rootModel.get().setWorkingdir(path.getParentFile());
      rootModel.get().setFilename(path.getName());
      ExporterFacade.exportSession(rootModel.get(), ExporterFacade.ExportFormat.XML, path);
    } catch (IOException | ExportException exception) {
      AlertFactory.createAlert(exception).showAndWait();
    }
  }

  private void saveCode(ActionEvent t) {
    // Set the code filename, if no filename set yet
    Code code = rootModel.get().getScenario().getCode();
    if (code.getFilename().isEmpty()) {
      FileChooser fileChooser =
          FileChooserFactory.createSaveFileChooser(CODE, rootModel.get().getWorkingdir());
      File chosenFile = fileChooser.showSaveDialog(view.getScene().getWindow());
      if (chosenFile == null) {
        return;
      }
      code.setFilename(chosenFile.getAbsolutePath());
    }
    // Export the code to the file
    try {
      ExporterFacade.exportCode(code, false);
    } catch (IOException e) {
      AlertFactory.createAlert(e).showAndWait();
    }
  }

  private void saveSpec(ActionEvent t) {
    try {
      ConstraintSpecification spec = rootModel.get().getScenario().getActiveSpec();
      if (spec == null) { // There is no active specification tab open yet
        AlertFactory.createAlert(Alert.AlertType.ERROR, "Save Specification",
            "No specification available.", "").showAndWait();
      } else {
        FileChooser fileChooser = FileChooserFactory.createSaveFileChooser(SPECIFICATION,
            rootModel.get().getWorkingdir());
        File specFile = fileChooser.showSaveDialog(view.getScene().getWindow());
        ExporterFacade.exportSpec(spec, ExporterFacade.ExportFormat.XML, specFile);
      }
    } catch (ExportException | IOException e) {
      AlertFactory.createAlert(e).showAndWait();
    }
  }


  @Override
  public StvsMenuBar getView() {
    return view;
  }

  private class HistoryFilenamesChangeListener
      implements javafx.collections.ListChangeListener<String> {

    @Override
    public void onChanged(Change<? extends String> change) {
      updateHistoryMenu();
    }
  }
}
