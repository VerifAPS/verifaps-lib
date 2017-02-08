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
      cells.put(entry.getKey(), bindCell(entry.getKey(), entry.getValue()));
    }
    return cells;
  }

  private static <C extends CellOperationProvider> HybridCellModel<C> bindCell(String column, C cell) {
    return new HybridCellModel<>(column, cell);
  }

  private final HybridCellModel<ConstraintDuration> durationCell;
  private final SpecificationRow<ConstraintCell> sourceRow;

  public SynchronizedRow(SpecificationRow<ConstraintCell> sourceRow, ConstraintDuration duration) {
    super(createCellsFromRow(sourceRow, duration));
    this.sourceRow = sourceRow;
    this.durationCell = bindCell("Duration", duration);
    // Create bindings to all other stuff
    this.commentProperty().bindBidirectional(sourceRow.commentProperty());
    sourceRow.getCells().addListener(this::onCellChanges);
  }

  protected void onCellChanges(MapChangeListener.Change<? extends String, ? extends ConstraintCell> change) {
    if (change.wasAdded()) {
      getCells().put(change.getKey(), bindCell(change.getKey(), change.getValueAdded()));
    }
    if (change.wasRemoved()) {
      getCells().remove(change.getKey());
    }
  }

  public HybridCellModel<ConstraintDuration> getDuration() {
    return durationCell;
  }

  public SpecificationRow<ConstraintCell> getSourceRow() {
    return sourceRow;
  }
}
