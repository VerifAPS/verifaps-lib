package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import java.util.*

/**
 * Is notified by the [Z3Solver] after concretization.
 */
fun interface OptionalConcreteSpecificationHandler {
    /**
     * Performs this operation on the given concreteSpecification.
     *
     * @param optionalConcreteSpecification the concreteSpecification argument
     */
    fun accept(optionalConcreteSpecification: Optional<ConcreteSpecification?>?)
}
