package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.logic.specification.ConcretizationException;
import edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import edu.kit.iti.formal.stvs.util.ThrowableHandler;

import java.util.List;

/**
 * Concretizer that uses Z3 to solve its systems generated from {@link ValidSpecification}.
 *
 * @author Leon Kaucher
 */
public class SmtConcretizer implements SpecificationConcretizer {
  private final GlobalConfig config;
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
   * Delegates the solving task to the Z3-Process and registers handlers for the result and
   * exceptions.
   * 
   * @param validSpecification The valid specification that should be conretized
   * @param freeVariables FreeVariables that were used in the {@code validSpecification}
   */
  @Override
  public ConcreteSpecification calculateConcreteSpecification(ValidSpecification validSpecification,
      List<ValidFreeVariable> freeVariables) throws ConcretizationException {
    SmtEncoder encoder =
        new SmtEncoder(config.getMaxLineRollout(), validSpecification, freeVariables);
    return z3Solver.concretizeSmtModel(encoder.getConstraint(),
        validSpecification.getColumnHeaders());
  }

  /**
   * Terminates the calculation of the concrete specification.
   */
  @Override
  public void terminate() {
    Process runningProcess = z3Solver.getProcess();
    if (runningProcess != null && runningProcess.isAlive()) {
      runningProcess.destroy();
    }
  }
}
