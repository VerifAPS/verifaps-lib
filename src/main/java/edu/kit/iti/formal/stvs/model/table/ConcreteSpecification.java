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
    this(new HashMap<>(), new ArrayList<>(), isCounterExample);
  }

  public ConcreteSpecification(Map<String, SpecificationColumn<ConcreteCell>> columns,
                               List<ConcreteDuration> durations, boolean isCounterExample) {
    super(columns, durations);
    this.isCounterExample = isCounterExample;
  }

  public boolean isCounterExample() {
    return isCounterExample;
  }

  /**
   * A row in a ConcreteSpecification is not the same as a row in a ConstraintSpecification.
   * This function does the mapping between the two.
   */
  public List<ConcreteCell> getConcreteValuesForConstraint(String column, int constraintRow) {
    int startIndex = durations.get(constraintRow).getBeginCycle();
    int endIndex = durations.get(constraintRow).getEndCycle();
    ArrayList<ConcreteCell> concreteCells = new ArrayList<>();
    for (int i = startIndex; i < endIndex; i++) {
      concreteCells.add(getCell(i, column));
    }
    return concreteCells;
  }
}
