package edu.kit.iti.formal.stvs.view.spec.table.cells;

import edu.kit.iti.formal.stvs.model.table.CellOperationProvider;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.StringProperty;

/**
 * Is Cell for Durations-Constraint-Expressions and Variable-Constaint-Expressions
 */
public class ValueCellController implements Controller {
  private final CellOperationProvider cellModel;
  private final GlobalConfig globalConfig;
  private ValueCell valueCell;

  /**
   * Listens if model cell changes
   */
  private void onAddUserInputStringChanged(String string) {
  }

  private StringProperty value;

  public ValueCellController(CellOperationProvider cellModel, GlobalConfig globalConfig) {
    this.cellModel = cellModel;
    this.globalConfig = globalConfig;
  }

  @Override
  public ValueCell getView() {
    return valueCell;
  }
}
