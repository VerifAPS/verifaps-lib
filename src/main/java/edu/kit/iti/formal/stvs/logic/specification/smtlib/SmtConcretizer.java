package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import edu.kit.iti.formal.stvs.util.ProcessOutputAsyncTask;

import java.util.List;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * Created by csicar on 08.02.17.
 */
public class SmtConcretizer implements SpecificationConcretizer {
  private final GlobalConfig config;
  private ProcessOutputAsyncTask task;

  public SmtConcretizer(GlobalConfig config) {
    this.config = config;
  }

  @Override
  public void calculateConcreteSpecification(ValidSpecification validSpecification,
                                             List<ValidFreeVariable> freeVariables,
                                             Consumer<Optional<ConcreteSpecification>> consumer,
                                             Consumer<Throwable> exceptionHandler) {
    SmtEncoder encoder = new SmtEncoder((i) -> config.getMaxLineRollout(), validSpecification,
        freeVariables);
    this.task = Z3Solver.concretizeSConstraint(encoder.getConstrain(), validSpecification.getColumnHeaders(), consumer);
    Thread.UncaughtExceptionHandler handler = (t, exception) -> {
      exceptionHandler.accept(exception);
    };
    this.task.setUncaughtExceptionHandler(handler);
    this.task.start();
  }

  public void terminate() {
    if (task != null) {
      task.terminate();
    }
  }
}
