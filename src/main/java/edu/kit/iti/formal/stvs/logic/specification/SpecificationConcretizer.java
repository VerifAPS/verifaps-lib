package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.common.OptionalProperty;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;


/**
 * @author Benjamin Alt
 */
public interface SpecificationConcretizer {

  public ConcretizerContext getContext();

  public void setContext(ConcretizerContext context);

  /**
   * Launch a new simulation after a specification change, unless one is already running
   *
   * @param spec The changed spec
   */
  public void createConcreteSpecification(ValidSpecification spec);

  /**
   * Get the current concrete specification.
   * @return The concrete specification or null if no concrete specification exists.
   */
  public ConcreteSpecification getConcreteSpec();

  public OptionalProperty<ConcreteSpecification> concreteSpecProperty();

  public void setConcreteSpec(ConcreteSpecification concreteSpec);
}

