package edu.kit.iti.formal.stvs.model.table;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author Benjamin Alt
 */
public class ConcreteSpecification extends SpecificationTable<ConcreteCell, ConcreteDuration> {

  private final boolean isCounterExample;

  public ConcreteSpecification(boolean isCounterExample) {
    this(new ArrayList<>(), new ArrayList<>(), isCounterExample);
  }

  public ConcreteSpecification(List<SpecificationRow<ConcreteCell>> rows,
                               List<ConcreteDuration> durations,
                               boolean isCounterExample) {
    super();
    this.isCounterExample = isCounterExample;

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
    int startIndex = durations.get(constraintRow).getBeginCycle();
    int endIndex = durations.get(constraintRow).getEndCycle();

    ArrayList<ConcreteCell> concreteCells = new ArrayList<>();
    SpecificationColumn<ConcreteCell> concreteColumn = getColumnByName(column);

    for (int i = startIndex; i < endIndex; i++) {
      concreteCells.add(concreteColumn.getCells().get(i));
    }
    return concreteCells;
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
