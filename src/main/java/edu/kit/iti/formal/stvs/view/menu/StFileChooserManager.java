package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;

/**
 * Created by csicar on 10.01.17.
 */
public class StFileChooserManager {
  public StFileChooserManager(Code code, GlobalConfig globalConfig) {

    this.globalConfig = globalConfig;
  }

  private GlobalConfig globalConfig;

}
