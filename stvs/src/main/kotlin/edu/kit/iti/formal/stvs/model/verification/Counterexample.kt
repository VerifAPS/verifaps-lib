package edu.kit.iti.formal.stvs.model.verification

import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import java.io.File
import java.util.*

/**
 * A [VerificationResult] with a counterexample.
 * @author Benjamin Alt
 */
class Counterexample(val counterexample: ConcreteSpecification, override val logFile: File) : VerificationResult {
    /**
     * Create a new Counterexample from a given [ConcreteSpecification] and a log file.
     * @param counterexample The concrete specification (counterexample)
     * @param logFile The log file
     */
    init {
        assert(counterexample.isCounterExample)
    }

    override fun accept(visitor: VerificationResultVisitor) {
        visitor.visitCounterexample(this)
    }
}
