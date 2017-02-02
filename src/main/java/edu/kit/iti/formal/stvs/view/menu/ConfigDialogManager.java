package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import javafx.scene.control.Dialog;

/**
 * Created by csicar on 11.01.17.
 */
public class ConfigDialogManager extends Dialog<GlobalConfig> {
  private GlobalConfig config;

  public ConfigDialogManager(GlobalConfig config) {
    this.setTitle("Configuration-Dialog");
  }


}
