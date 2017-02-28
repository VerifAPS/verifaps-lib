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
 * Created by Philipp on 01.02.2017.
 *
 * @author Philipp
 */
public class HybridRow extends SpecificationRow<HybridCell<ConstraintCell>> {

  private static Map<String, HybridCell<ConstraintCell>> createCellsFromRow(
      SpecificationRow<ConstraintCell> subscribingRow) {
    Map<String, HybridCell<ConstraintCell>> cells = new HashMap<>();
    for (Map.Entry<String, ConstraintCell> entry : subscribingRow.getCells().entrySet()) {
      HybridCell<ConstraintCell> hybridCell = new HybridCell<>(entry.getKey(), entry.getValue());
      cells.put(entry.getKey(), hybridCell);
    }
    return cells;
  }

  private final HybridCell<ConstraintDuration> durationCell;
  private final SpecificationRow<ConstraintCell> sourceRow;

  public HybridRow(SpecificationRow<ConstraintCell> sourceRow, ConstraintDuration duration) {
    super(createCellsFromRow(sourceRow),
        hybridCell -> new Observable[] {hybridCell.stringRepresentationProperty(),
            hybridCell.commentProperty(), hybridCell.counterExamplesProperty()});
    this.sourceRow = sourceRow;
    this.durationCell = new HybridCell<>("Duration", duration);
    sourceRow.getCells().addListener(this::onSourceCellsChange);
    // Create bindings to all other stuff
    this.commentProperty().bindBidirectional(sourceRow.commentProperty());
  }

  private void onSourceCellsChange(
      MapChangeListener.Change<? extends String, ? extends ConstraintCell> change) {
    if (change.wasAdded()) {
      getCells().put(change.getKey(), new HybridCell<>(change.getKey(), change.getValueAdded()));
    }
    if (change.wasRemoved()) {
      getCells().put(change.getKey(), new HybridCell<>(change.getKey(), change.getValueRemoved()));
    }
  }

  public HybridCell<ConstraintDuration> getDuration() {
    return durationCell;
  }

  public SpecificationRow<ConstraintCell> getSourceRow() {
    return sourceRow;
  }

  public void updateCounterExampleCells(int rowIndex,
      Optional<ConcreteSpecification> counterExample) {
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

  public List<String> createCounterExampleCells(String columnId, int rowIndex,
      ConcreteSpecification counterExample) {
    return counterExample.getConcreteValuesForConstraintCell(columnId, rowIndex).stream()
        .map(cell -> cell.getValue().getValueString()).collect(Collectors.toList());
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
