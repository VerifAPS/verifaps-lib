package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;

import java.util.function.Consumer;

/**
 * Created by bal on 11.01.17.
 */
public interface SpecificationConcretizer {

  public void addSuccessfulConcretizationListener(Consumer<ConcreteSpecification> listener);

  public ConcretizerContext getContext();

  public void setContext(ConcretizerContext context);

  public void createConcreteSpecification();

  /**
   * Launch a new simulation after a specification change, unless one is already running
   *
   * @param spec The changed spec
   */
  public void onSpecificationChanged(ValidSpecification spec);
}

