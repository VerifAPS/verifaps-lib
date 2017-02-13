package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer;
import edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizerState;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;

import java.io.IOException;
import java.util.List;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * Created by csicar on 08.02.17.
 */
public class SMTConcretizer implements SpecificationConcretizer {
  private ValidSpecification validSpecification;
  private GlobalConfig config;
  private Optional<ConcreteSpecification> concreteSpecification;
  private SmtEncoder encoder;
  private List<Consumer<SpecificationConcretizerState>> eventListeners;
  private SpecificationConcretizerState concretizerState;

  public SMTConcretizer(ValidSpecification validSpecification, GlobalConfig config,
                        List<ValidFreeVariable> freeVariables) {
    this.validSpecification = validSpecification;
    this.config = config;
    this.encoder = new SmtEncoder((i) -> config.getMaxLineRollout(), validSpecification,
        freeVariables);
    this.concreteSpecification = Optional.empty();
    this.concretizerState = SpecificationConcretizerState.IDLE;

  }

  @Override
  public Optional<ConcreteSpecification> calculateConcreteSpecification() throws IOException {
    this.concreteSpecification = Z3Solver.concretizeSConstraint(encoder
        .getConstrain(), validSpecification.getColumnHeaders());
    this.concretizerState = SpecificationConcretizerState.FINISHED;
    fireListeners();
    return this.concreteSpecification;
  }

  @Override
  public Optional<ConcreteSpecification> getConcreteSpecification() {
    return concreteSpecification;
  }

  private void fireListeners() {
    eventListeners.forEach(eventListener -> eventListener.accept(this.concretizerState));
  }

  @Override
  public void addEventListener(Consumer<SpecificationConcretizerState> eventListener) {
    eventListeners.add(eventListener);
  }
}
