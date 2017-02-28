package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import edu.kit.iti.formal.stvs.util.ProcessOutputAsyncTask;
import edu.kit.iti.formal.stvs.util.ThrowableHandler;

import java.util.List;

/**
 * Concretizer that uses Z3 to solve its systems generated from {@link ValidSpecification}.
 *
 * @author Leon Kaucher
 */
public class SmtConcretizer implements SpecificationConcretizer {
  private final GlobalConfig config;
  private ProcessOutputAsyncTask task;
  private Z3Solver z3Solver;

  /**
   * Creates a concretizer.
   *
   * @param config configuration for the solver
   */
  public SmtConcretizer(GlobalConfig config) {
    this.config = config;
    this.z3Solver = new Z3Solver(config);
  }

  /**
   * Delegates the solving task to the Z3-Process and registers handlers for the
   * result and exceptions.
   *
   * @param validSpecification   The valid specification that should be conretized
   * @param freeVariables        FreeVariables that were used in the {@code validSpecification}
   * @param specificationHandler handles the concrete specification
   *                             (or an empty {@link java.util.Optional}) if result not present
   * @param exceptionHandler     handles exceptions
   */
  @Override
  public void calculateConcreteSpecification(ValidSpecification validSpecification,
                               List<ValidFreeVariable> freeVariables,
                               OptionalConcreteSpecificationHandler specificationHandler,
                               ThrowableHandler exceptionHandler) {
    SmtEncoder encoder = new SmtEncoder(config.getMaxLineRollout(), validSpecification,
        freeVariables);
    this.task = z3Solver.concretizeSmtModel(
        encoder.getConstraint(),
        validSpecification.getColumnHeaders(),
        specificationHandler);
    Thread.UncaughtExceptionHandler handler =
        (t, exception) -> exceptionHandler.handleThrowable(exception);
    this.task.setUncaughtExceptionHandler(handler);
    this.task.start();
  }

  /**
   * Terminates the concretization.
   */
  public void terminate() {
    if (task != null) {
      task.terminate();
    }
  }
}
