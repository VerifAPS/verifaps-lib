package edu.kit.iti.formal.stvs.view.spec.table.rowActions;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.spec.table.DurationsColumnController;
import edu.kit.iti.formal.stvs.view.spec.table.cells.HybridCellController;

/**
 * Controller of column next to the table which holds remove buttons for rows
 * Fires RowEvent with REMOVE_ROW EventType on View
 */
public class RemoveButtonColumnController extends RowActionColumnController {
  private RemoveButtonColumn view;
  private GlobalConfig globalConfig;

  public RemoveButtonColumnController(DurationsColumnController durations, GlobalConfig globalConfig) {
    super(durations);
    this.globalConfig = globalConfig;
  }

  @Override
  public void removeButton(int row) {

  }

  @Override
  public void addButton(int row, HybridCellController cell) {

  }

  public RemoveButtonColumn getView() {
    return view;
  }
}
