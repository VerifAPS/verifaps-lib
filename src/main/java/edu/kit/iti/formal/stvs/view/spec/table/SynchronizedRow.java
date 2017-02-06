package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.table.*;
import javafx.collections.MapChangeListener;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by Philipp on 01.02.2017.
 */
public class SynchronizedRow extends SpecificationRow<HybridCellModel<ConstraintCell>> {

  private static Map<String, HybridCellModel<ConstraintCell>> createCellsFromRow(SpecificationRow<ConstraintCell> subscribingRow, ConstraintDuration duration) {
    Map<String, HybridCellModel<ConstraintCell>> cells = new HashMap<>();
    for (Map.Entry<String, ConstraintCell> entry : subscribingRow.getCells().entrySet()) {
      cells.put(entry.getKey(), bindCell(entry.getValue()));
    }
    return cells;
  }

  private static <C extends CellOperationProvider> HybridCellModel<C> bindCell(C cell) {
    return new HybridCellModel<>(cell);
  }



  private final HybridCellModel<ConstraintDuration> durationCell;

  public SynchronizedRow(SpecificationRow<ConstraintCell> subscribingRow, ConstraintDuration duration) {
    super(createCellsFromRow(subscribingRow, duration));
    this.durationCell = bindCell(duration);
    // Create bindings to all other stuff
    this.commentProperty().bindBidirectional(subscribingRow.commentProperty());
    subscribingRow.getCells().addListener(this::onCellChanges);
  }

  public HybridCellModel<ConstraintDuration> getDuration() {
    return durationCell;
  }

  protected void onCellChanges(MapChangeListener.Change<? extends String, ? extends ConstraintCell> change) {
    if (change.wasAdded()) {
      getCells().put(change.getKey(), bindCell(change.getValueAdded()));
    }
    if (change.wasRemoved()) {
      getCells().remove(change.getKey());
    }
  }
}
