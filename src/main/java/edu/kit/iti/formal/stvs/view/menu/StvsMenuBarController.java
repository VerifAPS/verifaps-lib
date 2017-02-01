package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.common.ErrorMessageDialog;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.scene.control.Alert;
import javafx.scene.control.Label;
import javafx.stage.FileChooser;
import javafx.stage.Popup;
import javafx.stage.Stage;

import java.io.*;
import java.util.Optional;

/**
 * Created by csicar on 10.01.17.
 * Controller for the MenuBar at the top of the window
 * does just fire to the root controller
 */
public class StvsMenuBarController implements Controller {
  private StvsMenuBar view;
  private StvsRootModel rootModel;

  /**
   * create a StvsMenuBarController; the parameters will be modified.
   * @param rootModel the applications root model
   */
  public StvsMenuBarController(StvsRootModel rootModel) {
    //set own properties
    this.rootModel = rootModel;

    //create view
    this.view = new StvsMenuBar();


    //add listener
    view.open.setOnAction(this::openFile);
    view.saveAll.setOnAction(this::saveAll);
    view.saveCode.setOnAction(this::saveCode);
    view.saveSpec.setOnAction(this::saveSpec);
    view.config.setOnAction(this::openConfigDialog);


  }

  private void openConfigDialog(ActionEvent t) {
    ConfigDialogManager manager = new ConfigDialogManager(rootModel.getGlobalConfig());
    Optional<GlobalConfig> newConfig = manager.showAndWait();
    newConfig.ifPresent(config -> {
      //rootModel.getGlobalConfig() = config;
    });
  }

  private void openFile(ActionEvent t) {
    FileChooser fileChooser = new FileChooser();
    fileChooser.setTitle("Open file");
    fileChooser.setInitialDirectory(rootModel.getWorkingdir());
    File chosenFile = fileChooser.showOpenDialog(view.getScene().getWindow());
    if(chosenFile != null) {
      try {
        ImporterFacade.importFile(chosenFile, (constraintSpecification) -> {
            rootModel.getHybridSpecifications().addAll(constraintSpecification);
        });
      } catch (IOException e) {
        new ErrorMessageDialog(e);
      }
    }
  }

  private void saveAll(ActionEvent t) {
    FileChooser fileChooser = new FileChooser();
    fileChooser.setTitle("Save session");
    fileChooser.setInitialDirectory(rootModel.getWorkingdir());
    File chosenFile = fileChooser.showOpenDialog(view.getScene().getWindow());
    if(chosenFile != null) {
      try {
        ExporterFacade.exportSession(rootModel, ExporterFacade.ExportFormat
            .XML, chosenFile);

      } catch (IOException e) {
        new ErrorMessageDialog(e);
      }
    }
  }

  private void saveCode(ActionEvent t) {
    // Todo: implement
    Code code = rootModel.getScenario().getCode();
    try {
      ExporterFacade.exportCode(code);
    } catch (IOException e) {
      new ErrorMessageDialog(e);
    }
  }

  private void saveSpec(ActionEvent t) {
    // Todo: implement
  }


  @Override
  public StvsMenuBar getView() {
    return view;
  }
}
