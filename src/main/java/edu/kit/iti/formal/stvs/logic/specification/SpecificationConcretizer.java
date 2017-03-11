package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.logic.specification.smtlib.OptionalConcreteSpecificationHandler;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import edu.kit.iti.formal.stvs.util.ThrowableHandler;

import java.util.List;


/**
 * Interface a concretizer must implement. Concretizers create a {@link ConcreteSpecification}
 * (a concrete instance of a specification table) from a {@link ValidSpecification}.
 *
 * @author Benjamin Alt
 */
public interface SpecificationConcretizer {

  /**
   * Create a concrete instance from a given valid constraint specification and a list of free
   * variables.
   *
   * @param validSpecification The valid specification that should be concretized
   * @param freeVariables FreeVariables that were used in the {@link ValidSpecification}
   */
  ConcreteSpecification calculateConcreteSpecification(
      ValidSpecification validSpecification,
      List<ValidFreeVariable> freeVariables)
      throws ConcretizationException;

  /**
   * Terminates the calculation of the concrete specification.
   */
  void terminate();
}

