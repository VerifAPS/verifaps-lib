package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.expressions.Value;
import edu.kit.iti.formal.stvs.model.table.*;
import javafx.beans.Observable;
import javafx.collections.MapChangeListener;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Created by Philipp on 01.02.2017.
 */
public class SynchronizedRow extends SpecificationRow<HybridCellModel<ConstraintCell>> {

  private static Map<String, HybridCellModel<ConstraintCell>> createCellsFromRow(
      SpecificationRow<ConstraintCell> subscribingRow) {
    Map<String, HybridCellModel<ConstraintCell>> cells = new HashMap<>();
    for (Map.Entry<String, ConstraintCell> entry : subscribingRow.getCells().entrySet()) {
      HybridCellModel<ConstraintCell> hybridCell =
          new HybridCellModel<>(entry.getKey(), entry.getValue());
      cells.put(entry.getKey(), hybridCell);
    }
    return cells;
  }

  private final HybridCellModel<ConstraintDuration> durationCell;
  private final SpecificationRow<ConstraintCell> sourceRow;

  public SynchronizedRow(
      SpecificationRow<ConstraintCell> sourceRow,
      ConstraintDuration duration) {
    super(
        createCellsFromRow(sourceRow),
        hybridCell -> new Observable[] {
            hybridCell.stringRepresentationProperty(),
            hybridCell.commentProperty(),
            hybridCell.counterExamplesProperty()
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

  public void updateCounterExampleCells(int rowIndex, Optional<ConcreteSpecification> counterExample) {
    if (counterExample.isPresent()) {
      for (Map.Entry<String, HybridCellModel<ConstraintCell>> entry : getCells().entrySet()) {
        entry.getValue().counterExamplesProperty().setAll(createCounterExampleCells(entry.getKey(), rowIndex, counterExample.get()));
      }
      durationCell.counterExamplesProperty().setAll(
          counterExample.get().getConcreteDurationForConstraintRow(rowIndex)
              .map(ConcreteDuration::getDuration)
              .map(i -> Integer.toString(i))
              .map(Collections::singletonList)
              .orElse(Collections.emptyList()));
    } else {
      durationCell.clearCounterExample();
    }
  }

  public List<String> createCounterExampleCells(String columnId, int rowIndex, ConcreteSpecification counterExample) {
    return counterExample.getConcreteValuesForConstraintCell(columnId, rowIndex).stream()
        .map(cell -> cell.getValue().getValueString())
        .collect(Collectors.toList());
  }
}
