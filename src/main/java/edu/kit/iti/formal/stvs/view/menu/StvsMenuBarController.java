package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.ObservableList;

/**
 * Created by csicar on 10.01.17.
 * Controller for the MenuBar at the top of the window
 * does just fire to the root controller
 */
public class StvsMenuBarController implements Controller {
  private StvsMenuBar view;
  private GlobalConfig globalConfig;

  public StvsMenuBarController(ObservableList<HybridSpecification> hybridSpecifications, Code code, GlobalConfig globalConfig) {

    this.globalConfig = globalConfig;
  }

  @Override
  public StvsMenuBar getView() {
    return view;
  }
}
