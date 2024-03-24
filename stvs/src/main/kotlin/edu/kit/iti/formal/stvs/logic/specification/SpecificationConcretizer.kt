package edu.kit.iti.formal.stvs.logic.specification

import edu.kit.iti.formal.stvs.logic.specification.ConcretizationException
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.ValidSpecification

/**
 * Interface a concretizer must implement. Concretizers create a [ConcreteSpecification]
 * (a concrete instance of a specification table) from a [ValidSpecification].
 *
 * @author Benjamin Alt
 */
interface SpecificationConcretizer {
    /**
     * Create a concrete instance from a given valid constraint specification and a list of free
     * variables.
     *
     * @param validSpecification The valid specification that should be concretized
     * @param freeVariables FreeVariables that were used in the [ValidSpecification]
     * @return calculated concrete specification
     * @throws ConcretizationException general error during concretization
     */
    @Throws(ConcretizationException::class)
    fun calculateConcreteSpecification(
        validSpecification: ValidSpecification?,
        freeVariables: List<ValidFreeVariable>
    ): ConcreteSpecification?

    /**
     * Terminates the calculation of the concrete specification.
     */
    fun terminate()
}

