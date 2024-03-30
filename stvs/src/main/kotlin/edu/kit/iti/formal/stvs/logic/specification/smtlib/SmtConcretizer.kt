package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.stvs.logic.specification.ConcretizationException
import edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.ValidSpecification

/**
 * Concretizer that uses Z3 to solve its systems generated from [ValidSpecification].
 *
 * @author Leon Kaucher
 */
class SmtConcretizer(private val config: GlobalConfig) : SpecificationConcretizer {
    private val z3Solver = Z3Solver(config)

    /**
     * Delegates the solving task to the Z3-Process and registers handlers for the result and
     * exceptions.
     *
     * @param validSpecification The valid specification that should be conretized
     * @param freeVariables FreeVariables that were used in the `validSpecification`
     */
    @Throws(ConcretizationException::class)
    override fun calculateConcreteSpecification(
        validSpecification: ValidSpecification,
        freeVariables: List<ValidFreeVariable>
    ): ConcreteSpecification {
        val encoder =
            SmtEncoder(config.maxLineRollout, validSpecification, freeVariables)
        return z3Solver.concretizeSmtModel(
            encoder.constraint,
            validSpecification.columnHeaders
        )
    }

    /**
     * Terminates the calculation of the concrete specification.
     */
    override fun terminate() {
        val runningProcess = z3Solver.process
        if (runningProcess != null && runningProcess.isAlive) {
            runningProcess.destroy()
        }
    }
}
