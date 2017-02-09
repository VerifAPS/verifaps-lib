package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import de.tudresden.inf.lat.jsexp.Sexp;
import de.tudresden.inf.lat.jsexp.SexpFactory;
import de.tudresden.inf.lat.jsexp.SexpList;
import edu.kit.iti.formal.stvs.logic.specification.ConcretizerContext;
import edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer;
import edu.kit.iti.formal.stvs.model.common.OptionalProperty;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;

import java.util.Arrays;

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
    this.validSpecification = validSpecification;

  }

  @Override
  public ConcreteSpecification getConcreteSpec() {
    return null;
  }

  @Override
  public OptionalProperty<ConcreteSpecification> concreteSpecProperty() {
    return null;
  }

  @Override
  public void setConcreteSpec(ConcreteSpecification concreteSpec) {

  }
}
