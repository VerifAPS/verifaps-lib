package edu.kit.iti.formal.stvs.model.table;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * @author Benjamin Alt
 */
public class ConcreteSpecification extends SpecificationTable<ConcreteCell, ConcreteDuration> {

  private final boolean isCounterExample;

  public ConcreteSpecification(boolean isCounterExample) {
    super();
    this.isCounterExample = isCounterExample;
  }

  public ConcreteSpecification(Map<String, SpecificationColumn<ConcreteCell>> columns,
                               Map<Integer, ConcreteDuration> durations, boolean isCounterExample) {
    super(columns, durations);
    this.isCounterExample = isCounterExample;
  }

  public boolean isCounterExample() {
    return isCounterExample;
  }
}
