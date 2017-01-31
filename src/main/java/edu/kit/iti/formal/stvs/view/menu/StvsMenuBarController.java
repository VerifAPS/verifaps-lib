package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.stage.Stage;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
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


  }

  private void openFile(ActionEvent t) {

    //seems legit http://stackoverflow.com/a/31686775
    Stage stage = (Stage) this.getView().getScene().getWindow();

    StvsFileChooserManager manager = new StvsFileChooserManager(stage);
    manager.getFile().ifPresent((File file) -> {
      // TODO: handle opened file

    });
  }

  private void saveAll(ActionEvent t) {
    // Todo: implement
    ExporterFacade.exportSession(rootModel, ExporterFacade.ExportFormat.XML);
  }

  private void saveCode(ActionEvent t) {
    // Todo: implement
    Code code = rootModel.getScenario().getCode();
    BufferedWriter writer = null;
    try {
      File file = new File(code.getFilename());
      writer = new BufferedWriter(new FileWriter(file));
      writer.write(code.getSourcecode());
      writer.close();
    }catch(IOException e) {
      // TODO: show popup with errormessage
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
