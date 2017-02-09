package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.table.*;
import edu.kit.iti.formal.stvs.util.MapUtil;
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
        hybridCell -> new Observable[] { hybridCell.stringRepresentationProperty() });
    this.sourceRow = sourceRow;
    this.durationCell = new HybridCellModel<>("Duration", duration);
    // Create bindings to all other stuff
    this.commentProperty().bindBidirectional(sourceRow.commentProperty());
  }

  public HybridCellModel<ConstraintDuration> getDuration() {
    return durationCell;
  }

  public SpecificationRow<ConstraintCell> getSourceRow() {
    return sourceRow;
  }
}
