package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.common.OptionalProperty;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;

import java.util.function.Consumer;

/**
 * @author Benjamin Alt
 */
public abstract class SpecificationConcretizer {

  private OptionalProperty<ConcreteSpecification> concreteSpec;
  private ConcretizerContext context;

  public ConcretizerContext getContext() {
    return context;
  }

  public void setContext(ConcretizerContext context) {
    this.context = context;
  }

  /**
   * Launch a new simulation after a specification change, unless one is already running
   *
   * @param spec The changed spec
   */
  public abstract void createConcreteSpecification(ValidSpecification spec);

  public ConcreteSpecification getConcreteSpec() {
    return concreteSpec.get();
  }

  public OptionalProperty<ConcreteSpecification> concreteSpecProperty() {
    return concreteSpec;
  }

  public void setConcreteSpec(ConcreteSpecification concreteSpec) {
    this.concreteSpec.set(concreteSpec);
  }
}

