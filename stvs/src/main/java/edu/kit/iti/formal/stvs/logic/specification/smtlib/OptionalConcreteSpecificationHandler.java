package edu.kit.iti.formal.stvs.logic.specification.smtlib;

import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;

import java.util.Optional;

/**
 * Is notified by the {@link Z3Solver} after concretization.
 */
@FunctionalInterface
public interface OptionalConcreteSpecificationHandler {
  /**
   * Performs this operation on the given concreteSpecification.
   *
   * @param optionalConcreteSpecification the concreteSpecification argument
   */
  void accept(Optional<ConcreteSpecification> optionalConcreteSpecification);
}
