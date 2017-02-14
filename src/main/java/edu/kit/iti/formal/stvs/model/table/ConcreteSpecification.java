package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import javafx.beans.Observable;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

/**
 * @author Benjamin Alt
 */
public class ConcreteSpecification extends SpecificationTable<ValidIoVariable, ConcreteCell, ConcreteDuration> {

  private final boolean isCounterExample;

  public ConcreteSpecification(boolean isCounterExample) {
    this(new ArrayList<>(), new ArrayList<>(), new ArrayList<>(), isCounterExample);
  }

  public ConcreteSpecification(List<ValidIoVariable> ioVariables, List<SpecificationRow<ConcreteCell>> rows,
                               List<ConcreteDuration> durations,
                               boolean isCounterExample) {
    super(p -> new Observable[0], p -> new Observable[0]);
    this.isCounterExample = isCounterExample;

    getColumnHeaders().setAll(ioVariables);
    getRows().addAll(rows);
    getDurations().addAll(durations);
  }

  public boolean isCounterExample() {
    return isCounterExample;
  }

  /**
   * A row in a ConcreteSpecification is not the same as a row in a ConstraintSpecification.
   * This function does the mapping between the two.
   */
  public List<ConcreteCell> getConcreteValuesForConstraintRow(String column, int constraintRow) {
    // Counterexamples stop after first mismatch
    // So we possibly don't have as many counterexample rows as constraint rows.
    if (constraintRow >= durations.size()) {
      return Collections.emptyList();
    }
    int startIndex = durations.get(constraintRow).getBeginCycle();
    int endIndex = durations.get(constraintRow).getEndCycle();

    ArrayList<ConcreteCell> concreteCells = new ArrayList<>();
    SpecificationColumn<ConcreteCell> concreteColumn = getColumnByName(column);

    for (int i = startIndex; i < endIndex; i++) {
      concreteCells.add(concreteColumn.getCells().get(i));
    }
    return concreteCells;
  }

  public Optional<ConcreteDuration> getConcreteDurationForConstraintRow(int constraintRow) {
    if (constraintRow >= durations.size()) {
      return Optional.empty();
    }
    return Optional.of(durations.get(constraintRow));
  }

  //Finds the row number in the constraint specification for a given cycle
  public int cycleToRowNumber(int cycle) {
    ConcreteDuration durationWithCycle = getDurations().stream()
        .filter(
            duration -> duration.getBeginCycle() <= cycle && duration.getEndCycle() > cycle
        )
        .findFirst()
        .orElseThrow(() -> new IllegalArgumentException("Cycle not found"));
    return getDurations().indexOf(durationWithCycle);
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    if (!super.equals(o)) return false;

    ConcreteSpecification that = (ConcreteSpecification) o;

    return isCounterExample() == that.isCounterExample();
  }

  @Override
  public int hashCode() {
    return (isCounterExample() ? 1 : 0);
  }
}
