package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.stage.Stage;

/**
 * Created by csicar on 10.01.17.
 * Controller for the MenuBar at the top of the window
 * does just fire to the root controller
 */
public class StvsMenuBarController implements Controller {
  private StvsMenuBar view;
  private GlobalConfig globalConfig;
  private ObservableList<HybridSpecification> hybridSpecificataions;
  private Code code;

  /**
   * create a StvsMenuBarController; the parameters will be modified.
   * @param hybridSpecifications hybridSpecifications
   * @param code code
   */
  public StvsMenuBarController(ObservableList<HybridSpecification> hybridSpecifications, Code code) {
    //set own properties
    this.hybridSpecificataions = hybridSpecifications;
    this.code = code;
    this.globalConfig = globalConfig;

    //create view
    this.view = new StvsMenuBar();


    //add listener
    view.open.setOnAction(this::openFile);


  }

  private void openFile(ActionEvent t) {

    //seems legit http://stackoverflow.com/a/31686775
    Stage stage = (Stage) this.getView().getScene().getWindow();

    StvsFileChooserManager manager = new StvsFileChooserManager(stage);
  }


  @Override
  public StvsMenuBar getView() {
    return view;
  }
}
