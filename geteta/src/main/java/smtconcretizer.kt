/**
 *
 * @author Alexander Weigl
 * @version 1 (12.10.18)
 */
package edu.kit.iti.formal.stvs.logic.specification

import de.tudresden.inf.lat.jsexp.Sexp
import de.tudresden.inf.lat.jsexp.SexpFactory
import edu.kit.iti.formal.stvs.logic.specification.smtlib.BitvectorUtils
import java.math.BigInteger
import java.util.*
import java.util.stream.Collectors


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
            validSpecification: ValidSpecification,
            freeVariables: List<ValidFreeVariable>): ConcreteSpecification

    /**
     * Terminates the calculation of the concrete specification.
     */
    fun terminate()
}


/**
 * Exception that gets thrown if concretization fails in general.
 */
class ConcretizationException : Exception {
    private var message: String? = null
    var originalException: Exception? = null
        private set

    constructor(message: String) {
        this.message = message
        originalException = null
    }

    /**
     * Creates an instance by wrapping an existent exception.
     *
     * @param e Exception that causes this exception
     */
    constructor(e: Exception) : super(e) {
        originalException = e
        message = e.message
    }

    override fun getMessage(): String? {
        return message
    }
}


/**
 * Is notified by the [Z3Solver] after concretization.
 */
interface OptionalConcreteSpecificationHandler {
    /**
     * Performs this operation on the given concreteSpecification.
     *
     * @param optionalConcreteSpecification the concreteSpecification argument
     */
    fun accept(optionalConcreteSpecification: ConcreteSpecification?)
}


