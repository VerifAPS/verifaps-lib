package edu.kit.iti.formal.stvs.model.verification

/**
 * A visitor for [VerificationResult]s.
 */
interface VerificationResultVisitor {
    /**
     * Visit a [Counterexample].
     * @param result Counterexample to visit.
     */
    fun visitCounterexample(result: Counterexample?)

    /**
     * Visit a [VerificationError].
     * @param result error to visit
     */
    fun visitVerificationError(result: VerificationError?)

    /**
     * Visit a [VerificationSuccess].
     * @param result success to visit
     */
    fun visitVerificationSuccess(result: VerificationSuccess?)
}
