package edu.kit.iti.formal.stvs.view.spec.table.cells;

import edu.kit.iti.formal.stvs.model.table.CellOperationProvider;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;

public class HybridCellController implements Controller {
  private StringProperty comment;
  private ObservableList<String> counterexamples;
  private StringProperty errorTooltip;
  private BooleanProperty errorInCell;
  private HybridCell hybridCell;
  private GlobalConfig globalConfig;
  private ContextMenu contextMenu;

  public ObservableList<String> getCounterexamples() {
    return null;
  }

  public StringProperty getValueProperty() {
    return null;
  }

  public StringProperty getCommentProperty() {
    return null;
  }

  private void onAddUserInputStringChanged(String string) {
  }

  public void onProblemOccured(ObjectProperty<SpecProblem> problem) {

  }

  public HybridCellController(CellOperationProvider cell, ObservableList<String> counterexamples, GlobalConfig globalConfig) {
    this.globalConfig = globalConfig;

  }

  public HybridCell getView() {
    return hybridCell;
  }
}
