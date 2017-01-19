package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import javafx.scene.control.ContextMenu;

public class TableOutputController extends TableCategoryController {
  private GlobalConfig globalConfig;
  private ContextMenu contextMenu;

  public TableOutputController(HybridSpecification spec, TablePaneController tablePaneController) {
    super("Output", spec, tablePaneController);
  }

  public void addIoVariable(String string) {

  }
}
