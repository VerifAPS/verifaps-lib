package edu.kit.iti.formal.stvs.model.table;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import javafx.beans.Observable;
import javafx.collections.MapChangeListener;

/**
 * <p>This is the model that is used by the
 * {@link edu.kit.iti.formal.stvs.view.spec.table.SpecificationTableController}'s
 * {@link javafx.scene.control.TableView} as rows. Unlike the rows of the
 * {@link ConstraintSpecification} these rows contain not {@link ConstraintCell}s, but
 * {@link HybridCell}s, so that both the constraint cells as well as counter example
 * values can be stored together in the model.</p>
 *
 * <p>Created by Philipp on 01.02.2017.</p>
 *
 * @author Philipp
 */
public class HybridRow extends SpecificationRow<HybridCell<ConstraintCell>> {

  private static Map<String, HybridCell<ConstraintCell>> createCellsFromRow(
      SpecificationRow<ConstraintCell> subscribingRow) {
    Map<String, HybridCell<ConstraintCell>> cells = new HashMap<>();
    for (Map.Entry<String, ConstraintCell> entry : subscribingRow.getCells().entrySet()) {
      HybridCell<ConstraintCell> hybridCell = new HybridCell<>(entry.getValue());
      cells.put(entry.getKey(), hybridCell);
    }
    return cells;
  }

  private final HybridCell<ConstraintDuration> durationCell;
  private final SpecificationRow<ConstraintCell> sourceRow;

  /**
   * Creates an observable hybrid row that is synchronized to the state of the given sourceRow and
   * the duration.
   *
   * @param sourceRow the source row out of a {@link ConstraintSpecification} to synchronize this
   *                  row's hybrid cells for constraint cells to
   * @param duration the source constraint duration to synchronize this row's hybrid cell for the
   *                 duration to
   */
  public HybridRow(SpecificationRow<ConstraintCell> sourceRow, ConstraintDuration duration) {
    super(createCellsFromRow(sourceRow),
        hybridCell -> new Observable[] {
            hybridCell.stringRepresentationProperty(),
            hybridCell.commentProperty(),
            hybridCell.counterExamplesProperty()
        });
    this.sourceRow = sourceRow;
    this.durationCell = new HybridCell<>(duration);
    sourceRow.getCells().addListener(this::onSourceCellsChange);
    // Create bindings to all other stuff
    this.commentProperty().bindBidirectional(sourceRow.commentProperty());
  }

  private void onSourceCellsChange(
      MapChangeListener.Change<? extends String, ? extends ConstraintCell> change) {
    if (change.wasAdded()) {
      getCells().put(change.getKey(), new HybridCell<>(change.getValueAdded()));
    }
    if (change.wasRemoved()) {
      getCells().put(change.getKey(), new HybridCell<>(change.getValueRemoved()));
    }
  }

  public HybridCell<ConstraintDuration> getDuration() {
    return durationCell;
  }

  public SpecificationRow<ConstraintCell> getSourceRow() {
    return sourceRow;
  }

  /**
   * Updates the counterexample cells from the given concrete specification's row. If
   * the given {@link ConcreteSpecification} is empty, it will reset the counter example cells
   * list to the empty list.
   *
   * @param rowIndex the constraint row to look for cells
   * @param counterExample the concrete specification to look for counterexample values
   */
  public void updateCounterExampleCells(
      int rowIndex, Optional<ConcreteSpecification> counterExample) {
    if (counterExample.isPresent()) {
      for (Map.Entry<String, HybridCell<ConstraintCell>> entry : getCells().entrySet()) {
        entry.getValue().counterExamplesProperty()
            .setAll(createCounterExampleCells(entry.getKey(), rowIndex, counterExample.get()));
      }
      durationCell.counterExamplesProperty()
          .setAll(counterExample.get().getConcreteDurationForConstraintRow(rowIndex)
              .map(ConcreteDuration::getDuration).map(i -> Integer.toString(i))
              .map(Collections::singletonList).orElse(Collections.emptyList()));
    } else {
      durationCell.clearCounterExample();
    }
  }

  private List<String> createCounterExampleCells(
      String columnId, int rowIndex, ConcreteSpecification counterExample) {
    return counterExample.getConcreteValuesForConstraintCell(columnId, rowIndex).stream()
        .map(cell -> cell.getValue().getValueString())
        .collect(Collectors.toList());
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }
    if (!super.equals(o)) {
      return false;
    }

    HybridRow hybridRow = (HybridRow) o;

    if (durationCell != null ? !durationCell.equals(hybridRow.durationCell)
        : hybridRow.durationCell != null) {
      return false;
    }
    return getSourceRow() != null ? getSourceRow().equals(hybridRow.getSourceRow())
        : hybridRow.getSourceRow() == null;
  }
}
