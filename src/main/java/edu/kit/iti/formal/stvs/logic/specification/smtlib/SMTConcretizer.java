package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.logic.specification.ConcretizerContext;
import edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer;
import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;

/**
 * Created by csicar on 08.02.17.
 */
public class SMTConcretizer implements SpecificationConcretizer {
  private ValidSpecification validSpecification;

  public SMTConcretizer() {

  }

  @Override
  public ConcretizerContext getContext() {
    return null;
  }

  @Override
  public void setContext(ConcretizerContext context) {

  }

  @Override
  public void createConcreteSpecification(ValidSpecification spec) {

  }

  @Override
  public ConcreteSpecification getConcreteSpec() {
    return null;
  }

  @Override
  public NullableProperty<ConcreteSpecification> concreteSpecProperty() {
    return null;
  }

  @Override
  public void setConcreteSpec(ConcreteSpecification concreteSpec) {

  }
}
