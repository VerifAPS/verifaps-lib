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
    this(new HashMap<String, SpecificationColumn<ConcreteCell>>(), new HashMap<Integer,
        ConcreteDuration>(), isCounterExample);
  }

  public ConcreteSpecification(Map<String, SpecificationColumn<ConcreteCell>> columns,
                               Map<Integer, ConcreteDuration> durations, boolean isCounterExample) {
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
  public List<ConcreteCell> getConcreteValuesForConstraint(String column, int row) {
    int startIndex = getDuration(row).getBeginCycle();
    int endIndex = getDuration(row).getEndCycle();
    ArrayList<ConcreteCell> concreteCells = new ArrayList<>();
    for (int i = startIndex; i < endIndex; i++) {
      concreteCells.add(getCell(i, column));
    }
    return concreteCells;
  }
}
