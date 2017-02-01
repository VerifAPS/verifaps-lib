package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.spec.table.cells.HybridCellController;
import javafx.beans.property.IntegerProperty;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;

import java.util.List;

public class DurationsColumnController extends ColumnController {
  private IntegerProperty width;
  private ObservableList<HybridCellController> cells;
  private DurationsColumn durationsColumn;
  private GlobalConfig globalConfig;
  private ContextMenu contextMenu;

  public IntegerProperty getWidthProperty() {
    return width;
  }

  public int getWidth() {
    return width.get();
  }

  public DurationsColumnController(ColumnConfig config, GlobalConfig globalConfig) {
    super(config);
    this.globalConfig = globalConfig;
  }

  public void onProblemsChange(List<SpecProblem> problems) {

  }

  public ObservableList<HybridCellController> getCells() {
    return cells;
  }

  @Override
  public DurationsColumn getView() {
    return durationsColumn;
  }
}
