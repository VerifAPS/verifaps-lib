package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.ViewUtils;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.common.ErrorMessageDialog;
import javafx.beans.property.ObjectProperty;
import javafx.event.ActionEvent;
import javafx.scene.control.Alert;
import javafx.stage.FileChooser;

import java.io.File;
import java.io.IOException;

/**
 * Created by csicar on 10.01.17.
 * Controller for the MenuBar at the top of the window
 * does just fire to the root controller
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
    //set own properties
    this.rootModel = rootModel;

    //create view
    this.view = new StvsMenuBar();

    //add listener
    view.newCode.setOnAction(this::createNewCode);
    view.newSpec.setOnAction(this::createNewSpec);
    view.open.setOnAction(this::openFile);
    view.openSession.setOnAction(this::openSession);
    view.openCode.setOnAction(this::openCode);
    view.openSpec.setOnAction(this::openSpec);
    view.saveAll.setOnAction(this::saveAll);
    view.saveCode.setOnAction(this::saveCode);
    view.saveSpec.setOnAction(this::saveSpec);
    view.config.setOnAction(this::openConfigDialog);

  }

  private void createNewSpec(ActionEvent actionEvent) {
    //TODO
  }

  private void createNewCode(ActionEvent actionEvent) {
    this.rootModel.get().getScenario().setCode(new Code("untitled", ""));
  }

  private void openConfigDialog(ActionEvent t) {
    ConfigDialogManager dialogManager = new ConfigDialogManager(rootModel.get().getGlobalConfig());
  }

  private void openCode(ActionEvent t) {
    FileChooser fileChooser = new FileChooser();
    fileChooser.setTitle("Open an st-file");
    fileChooser.setInitialDirectory(rootModel.get().getWorkingdir());
    File chosenFile = fileChooser.showOpenDialog(view.getScene().getWindow());

    if (chosenFile == null) {
      return;
    }
    try {
      Code code = ImporterFacade.importStCode(chosenFile);
      this.rootModel.get().getScenario().setCode(code);
    } catch (IOException e) {
      new ErrorMessageDialog(e);
    }
  }

  private void openSession(ActionEvent t) {
    FileChooser fileChooser = new FileChooser();
    fileChooser.setTitle("Open a session");
    fileChooser.setInitialDirectory(rootModel.get().getWorkingdir());
    File chosenFile = fileChooser.showOpenDialog(view.getScene().getWindow());

    if (chosenFile == null) {
      return;
    }
    try {
      StvsRootModel model = ImporterFacade.importSession(
          chosenFile, ImporterFacade.ImportFormat.XML, rootModel.get().getGlobalConfig());
      model.setWorkingdir(chosenFile.getParentFile());
      this.rootModel.set(model);
    } catch (IOException | ImportException exception) {
      new ErrorMessageDialog(exception);
    }
  }

  private void openSpec(ActionEvent t) {
    FileChooser fileChooser = new FileChooser();
    fileChooser.setTitle("Open a specification-file");
    fileChooser.setInitialDirectory(rootModel.get().getWorkingdir());
    File chosenFile = fileChooser.showOpenDialog(view.getScene().getWindow());

    if (chosenFile == null) {
      return;
    }
    try {
      HybridSpecification spec = ImporterFacade.importHybridSpec(chosenFile,
          ImporterFacade.ImportFormat.XML);
      this.rootModel.get().getHybridSpecifications().add(spec);

    } catch (IOException | ImportException e) {
      new ErrorMessageDialog(e);
    }
  }

  private void openFile(ActionEvent t) {
    //do only implement, when there is time left!!
    FileChooser fileChooser = new FileChooser();
    fileChooser.setTitle("Open file");
    fileChooser.setInitialDirectory(rootModel.get().getWorkingdir());
    File chosenFile = fileChooser.showOpenDialog(view.getScene().getWindow());

    if (chosenFile == null) {
      return;
    }
    try {
      ImporterFacade.importFile(chosenFile, rootModel.get().getGlobalConfig(), (hybridSpecification) -> {
        //handle hybridspecification
        rootModel.get().getHybridSpecifications().add(hybridSpecification);
      }, (rootModel) -> {
        //handle rootModel
        this.rootModel.setValue(rootModel);
      }, (code -> {
        //handle code
        this.rootModel.get().getScenario().setCode(code);
      }));
    } catch (IOException e) {
      new ErrorMessageDialog(e);
    }
  }


  private void saveAll(ActionEvent t) {
    FileChooser fileChooser = new FileChooser();
    fileChooser.setTitle("Save session");
    fileChooser.setInitialDirectory(rootModel.get().getWorkingdir());
    File chosenFile = fileChooser.showSaveDialog(view.getScene().getWindow());
    if (chosenFile != null) {
      try {
        ExporterFacade.exportSession(rootModel.get(), ExporterFacade.ExportFormat
            .XML, chosenFile);
      } catch (IOException | ExportException e) {
        new ErrorMessageDialog(e);
      }
    }
  }

  private void saveCode(ActionEvent t) {
    Code code = rootModel.get().getScenario().getCode();

    if (code.getFilename().isEmpty()) {
      FileChooser fileChooser = new FileChooser();
      fileChooser.setTitle("Select the file");
      fileChooser.setInitialDirectory(rootModel.get().getWorkingdir());
      File chosenFile = fileChooser.showSaveDialog(view.getScene().getWindow());
      if (chosenFile != null) {
        code.setFilename(chosenFile.getAbsolutePath());
      } else {
        return;
      }
    }
    try {
      ExporterFacade.exportCode(code, false);
    } catch (IOException e) {
      new ErrorMessageDialog(e);
    }
  }

  private void saveSpec(ActionEvent t) {
    try {
      ConstraintSpecification spec = rootModel.get().getScenario().getActiveSpec();
      if (spec == null) { // There is no active specification tab open yet
        ViewUtils.showDialog(Alert.AlertType.ERROR, "Save Specification", "No Specification available.", "");
      } else {
        ExporterFacade.exportSpec(spec, ExporterFacade.ExportFormat.XML);
      }
    } catch (ExportException e) {
      new ErrorMessageDialog(e);
    }
  }


  @Override
  public StvsMenuBar getView() {
    return view;
  }
}
