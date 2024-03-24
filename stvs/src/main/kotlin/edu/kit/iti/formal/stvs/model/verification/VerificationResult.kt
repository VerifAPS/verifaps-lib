package edu.kit.iti.formal.stvs.model.verification

import java.io.File

/**
 * The result of a verification (created by a
 * [edu.kit.iti.formal.stvs.logic.verification.VerificationEngine]).
 *
 * @author Benjamin Alt
 */
interface VerificationResult {
    /**
     * Accept a visitor.
     * @param visitor The visitor to visit this VerificationResult
     */
    fun accept(visitor: VerificationResultVisitor)

    /**
     * Get the log file (containing the output of the verification engine) or an empty Optional if
     * none is available. This would be the case if certain verification errors (such as
     * IOExceptions) occurred.
     *
     * @return The log file or an empty Optional if none is available
     */
    val logFile: File?
}
