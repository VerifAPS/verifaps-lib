package edu.kit.iti.formal.stvs.model.table;

/**
 * Created by philipp on 10.01.17.
 */
public class ConcreteSpecification extends SpecificationTable<ConcreteCell, ConcreteDuration> {

  private final boolean isCounterExample;


  /**
   * Copy constructor
   */
  public ConcreteSpecification(ConcreteSpecification spec) {
    //...
    isCounterExample = spec.isCounterExample;
  }

  public ConcreteSpecification(boolean isCounterExample) {
    this.isCounterExample = isCounterExample;
  }

  public boolean isCounterExample() {
    return isCounterExample;
  }
}
