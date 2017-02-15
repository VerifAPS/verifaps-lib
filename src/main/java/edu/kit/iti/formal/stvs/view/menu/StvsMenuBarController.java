package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.common.ErrorMessageDialog;
import javafx.beans.property.ObjectProperty;
import javafx.event.ActionEvent;
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
    view.open.setOnAction(this::openFile);
    view.openSession.setOnAction(this::openSession);
    view.openCode.setOnAction(this::openCode);
    view.openSpec.setOnAction(this::openSpec);
    view.saveAll.setOnAction(this::saveAll);
    view.saveCode.setOnAction(this::saveCode);
    view.saveSpec.setOnAction(this::saveSpec);
    view.config.setOnAction(this::openConfigDialog);

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
          chosenFile, ImporterFacade.ImportFormat.XML);
      model.setWorkingdir(chosenFile.getParentFile());
      this.rootModel.set(model);
    } catch (IOException | ImportException exception) {
      // TODO: Better visual for ImportException
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
          ImporterFacade
              .ImportFormat
              .XML);
       this.rootModel.get().getHybridSpecifications().add(spec);

    } catch (IOException | ImportException e) {
      // TODO: Show better message for import exception
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
      ImporterFacade.importFile(chosenFile, (hybridSpecification) -> {
        //handle hybridspecification
        rootModel.get().getHybridSpecifications().add(hybridSpecification);
      }, (rootModel) -> {
        //handle rootModel
        this.rootModel.setValue(rootModel);
      }, (verificationScenario) -> {
        // handle verification scenario
        this.rootModel.get().setScenario(verificationScenario);
      });
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

    if(code.getFilename().isEmpty()) {
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
    // Todo: implement

    HybridSpecification spec = null; // TODO: get the active tab's hybrid-specification
  }


  @Override
  public StvsMenuBar getView() {
    return view;
  }
}
