package edu.kit.iti.formal.stvs.model.verification

import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import java.io.*
import java.util.*

/**
 * The result of a verification (created by a
 * [edu.kit.iti.formal.stvs.logic.verification.VerificationEngine]).
 *
 * @author Benjamin Alt
 */
sealed class VerificationResult {
    /**
     * Accept a visitor.
     * @param visitor The visitor to visit this VerificationResult
     */
    fun <T> accept(visitor: VerificationResultVisitor<T>): T = when (this) {
        is VerificationSuccess -> visitor.visitVerificationSuccess(this)
        is VerificationError -> visitor.visitVerificationError(this)
        is Counterexample -> visitor.visitCounterexample(this)
        VerificationResultEmpty -> visitor.visitEmpty(this)
    }

    /**
     * Get the log (containing the output of the verification engine) or if
     * none is available. This would be the case if certain verification errors (such as
     * IOExceptions) occurred.
     *
     * @return The log file or an empty Optional if none is available
     */
    abstract val log: String?
}

data object VerificationResultEmpty : VerificationResult() {
    override val log: String? = null
}


/**
 * A [VerificationResult] indicating a successful verification (i.e. the code verified
 * against the specification).
 * @author Benjamin Alt
 */
data class VerificationSuccess(override val log: String) : VerificationResult()

/**
 * Errors related to the verification process.
 *
 * @author Benjamin Alt
 */
data class VerificationError(
    val reason: Reason,
    override var log: String
) : VerificationResult() {
    /**
     * Reasons why a [VerificationError] may occur.
     */
    enum class Reason(val errorMessage: String) {
        VERIFICATION_LAUNCH_ERROR("The verification could not be launched Check the verification engine command in the preferences dialog (Edit -> Preferences)"),
        NUXMV_NOT_FOUND("""The nuXmv executable could not be found. Check the path to the nuXmv executable in the preferences dialog (Edit -> Preferences)"""),
        PROCESS_ABORTED("The verification process has been aborted."),
        TIMEOUT("The verification timed out."),
        ERROR("An error occurred during verification."),
        EXCEPTION("An error occurred during verification."),
        UNKNOWN("An unknown error occurred during verification.")
    }
}


/**
 * A [VerificationResult] with a counterexample.
 * @author Benjamin Alt
 */
class Counterexample(
    val specification: ConstraintSpecification,
    val counterexample: ConcreteSpecification,
    override val log: String) : VerificationResult() {
    /**
     * Create a new Counterexample from a given [ConcreteSpecification] and a log file.
     * @param counterexample The concrete specification (counterexample)
     * @param logFile The log file
     */
    init {
        assert(counterexample.isCounterExample)
    }
}
