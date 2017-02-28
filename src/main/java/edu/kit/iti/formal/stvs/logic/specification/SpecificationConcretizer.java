package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.logic.specification.smtlib.OptionalConcreteSpecificationHandler;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import edu.kit.iti.formal.stvs.util.ThrowableHandler;

import java.util.List;


/**
 * Interface a concretizer must implement.
 *
 * @author Benjamin Alt
 */
public interface SpecificationConcretizer {

  /**
   * Must implement the solving task and registers handlers for the result and exceptions.
   *
   * @param validSpecification The valid specification that should be conretized
   * @param freeVariables FreeVariables that were used in the {@code validSpecification}
   * @param specificationHandler handles the concrete specification (or an empty
   *        {@link java.util.Optional}) if result not present
   * @param exceptionHandler handles exceptions
   */
  void calculateConcreteSpecification(ValidSpecification validSpecification,
      List<ValidFreeVariable> freeVariables,
      OptionalConcreteSpecificationHandler specificationHandler, ThrowableHandler exceptionHandler);

  /**
   * Terminates the concretization.
   */
  void terminate();
}

