package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

import javafx.beans.Observable;

/**
 * <p>
 * A concrete instance of a specification (i.e. a specification table with cells containing only
 * concrete values and concrete durations). Counterexamples and the results of the concretization of
 * a {@link ConstraintSpecification} (see
 * {@link edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer} are of this type.
 * </p>
 *
 * @author Benjamin Alt
 */
public class ConcreteSpecification
    extends SpecificationTable<ValidIoVariable, ConcreteCell, ConcreteDuration> {

  private final boolean isCounterExample;

  /**
   * Construct a new ConcreteSpecification with no rows or columns.
   *
   * @param isCounterExample True if this ConcreteSpecification is a counterexample
   */
  public ConcreteSpecification(boolean isCounterExample) {
    this(new ArrayList<>(), new ArrayList<>(), new ArrayList<>(), isCounterExample);
  }

  /**
   * Construct a new ConcreteSpecification with given column headers, rows and durations, but with a
   * default name.
   *
   * @param ioVariables The input/output variables defining the columns
   * @param rows The rows of concrete cells. One cycle corresponds to one row
   * @param durations The concrete durations. This list can be shorter than the number of rows,
   *        because for a duration of n there will be n rows.
   * @param isCounterExample True if this ConcreteSpecification is a counterexample
   */
  public ConcreteSpecification(List<ValidIoVariable> ioVariables,
      List<SpecificationRow<ConcreteCell>> rows, List<ConcreteDuration> durations,
      boolean isCounterExample) {
    this(DEFAULT_NAME, ioVariables, rows, durations, isCounterExample);
  }

  /**
   * Construct a new ConcreteSpecification with given name, column headers, rows and durations.
   *
   * @param name The name of this ConcreteSpecification
   * @param ioVariables The input/output variables defining the columns
   * @param rows The rows of concrete cells. One cycle corresponds to one row
   * @param durations The concrete durations. This list can be shorter than the number of rows,
   *        because for a duration of n there will be n rows.
   * @param isCounterExample True if this ConcreteSpecification is a counterexample
   */
  public ConcreteSpecification(String name, List<ValidIoVariable> ioVariables,
      List<SpecificationRow<ConcreteCell>> rows, List<ConcreteDuration> durations,
      boolean isCounterExample) {
    super(name, p -> new Observable[0], p -> new Observable[0]);
    this.isCounterExample = isCounterExample;

    getColumnHeaders().setAll(ioVariables);
    getRows().addAll(rows);
    getDurations().addAll(durations);
  }

  public boolean isCounterExample() {
    return isCounterExample;
  }

  /**
   * A row in a ConcreteSpecification is not the same as a row in a ConstraintSpecification: In a
   * ConcreteSpecification, a row corresponds to a cycle. One row in a ConstraintSpecification may
   * cover multiple cycles. This function returns the list of concrete values corresponding to a
   * constraint identified by its column and row (as in a ConstraintSpecification).
   *
   * @param column The column identifier for the constraint cell (the name of the input/output
   *        variable)
   * @param constraintRow The row of the constraint cell (according to the ConstraintSpecification
   *        row semantics, see description above)
   * @return The list of concrete cells corresponding to this concrete value
   */
  public List<ConcreteCell> getConcreteValuesForConstraintCell(String column, int constraintRow) {
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

  /**
   * Returns the concrete duration for a row in a {@link ConstraintSpecification}.
   *
   * @param constraintRow The index of a row in a {@link ConstraintSpecification}
   * @return The concrete duration assigned to the duration expression of the given row. The
   *         Optional return value is empty if there is no such duration (e.g. in a counterexample,
   *         where the error state is reached before the last row of the constraint specification)
   */
  public Optional<ConcreteDuration> getConcreteDurationForConstraintRow(int constraintRow) {
    if (constraintRow >= durations.size()) {
      return Optional.empty();
    }
    return Optional.of(durations.get(constraintRow));
  }

  /**
   * Maps a concrete cycle in this ConcreteSpecification to a row number in a constraint
   * specification.
   *
   * @param cycle The number of a cycle in this ConcreteSpecification
   * @return The number of the corresponding row in a ConstraintSpecification
   */
  public int cycleToRowNumber(int cycle) {
    ConcreteDuration durationWithCycle =
        getDurations().stream().filter(duration -> isCycleInDuration(cycle, duration)).findFirst()
            .orElseThrow(() -> new IllegalArgumentException("Cycle not found"));
    return getDurations().indexOf(durationWithCycle);
  }

  private static boolean isCycleInDuration(int cycle, ConcreteDuration duration) {
    return duration.getBeginCycle() <= cycle && duration.getEndCycle() > cycle;
  }

  @Override
  public int hashCode() {
    int result = super.hashCode();
    result = 31 * result + (isCounterExample() ? 1 : 0);
    return result;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null || getClass() != obj.getClass()) {
      return false;
    }
    if (!super.equals(obj)) {
      return false;
    }

    ConcreteSpecification that = (ConcreteSpecification) obj;

    return isCounterExample() == that.isCounterExample();
  }
}
