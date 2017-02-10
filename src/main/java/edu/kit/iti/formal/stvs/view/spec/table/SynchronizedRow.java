package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import javafx.beans.Observable;
import javafx.collections.MapChangeListener;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by Philipp on 01.02.2017.
 */
public class SynchronizedRow extends SpecificationRow<HybridCellModel<ConstraintCell>> {

  private static Map<String, HybridCellModel<ConstraintCell>> createCellsFromRow(
      SpecificationRow<ConstraintCell> subscribingRow) {
    Map<String, HybridCellModel<ConstraintCell>> cells = new HashMap<>();
    for (Map.Entry<String, ConstraintCell> entry : subscribingRow.getCells().entrySet()) {
      cells.put(entry.getKey(), new HybridCellModel<>(entry.getKey(), entry.getValue()));
    }
    return cells;
  }

  private final HybridCellModel<ConstraintDuration> durationCell;
  private final SpecificationRow<ConstraintCell> sourceRow;

  public SynchronizedRow(SpecificationRow<ConstraintCell> sourceRow, ConstraintDuration duration) {
    super(
        createCellsFromRow(sourceRow),
        hybridCell -> new Observable[] {
            hybridCell.stringRepresentationProperty(),
            hybridCell.commentProperty()
        });
    this.sourceRow = sourceRow;
    this.durationCell = new HybridCellModel<>("Duration", duration);
    sourceRow.getCells().addListener(this::onSourceCellsChange);
    // Create bindings to all other stuff
    this.commentProperty().bindBidirectional(sourceRow.commentProperty());
  }

  private void onSourceCellsChange(MapChangeListener.Change<? extends String, ? extends ConstraintCell> change) {
    if (change.wasAdded()) {
      getCells().put(change.getKey(), new HybridCellModel<>(change.getKey(), change.getValueAdded()));
    }
    if (change.wasRemoved()) {
      getCells().put(change.getKey(), new HybridCellModel<>(change.getKey(), change.getValueRemoved()));
    }
  }

  public HybridCellModel<ConstraintDuration> getDuration() {
    return durationCell;
  }

  public SpecificationRow<ConstraintCell> getSourceRow() {
    return sourceRow;
  }
}
