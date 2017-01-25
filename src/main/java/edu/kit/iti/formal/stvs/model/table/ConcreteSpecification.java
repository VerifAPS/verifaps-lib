package edu.kit.iti.formal.stvs.model.table;

/**
 * @author Benjamin Alt
 */
public class ConcreteSpecification extends SpecificationTable<ConcreteCell, ConcreteDuration> {

  private final boolean isCounterExample;

  public ConcreteSpecification(boolean isCounterExample) {
    super();
    this.isCounterExample = isCounterExample;
  }

  public boolean isCounterExample() {
    return isCounterExample;
  }
}
