/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.stvs.model.verification

import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification

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
data class VerificationError(val reason: Reason, override var log: String) : VerificationResult() {
    /**
     * Reasons why a [VerificationError] may occur.
     */
    enum class Reason(val errorMessage: String) {
        VERIFICATION_LAUNCH_ERROR(
            "The verification could not be launched Check the verification engine command in the preferences dialog (Edit -> Preferences)",
        ),
        NUXMV_NOT_FOUND(
            """The nuXmv executable could not be found. Check the path to the nuXmv executable in the preferences dialog (Edit -> Preferences)""",
        ),
        PROCESS_ABORTED("The verification process has been aborted."),
        TIMEOUT("The verification timed out."),
        ERROR("An error occurred during verification."),
        EXCEPTION("An error occurred during verification."),
        UNKNOWN("An unknown error occurred during verification."),
    }
}

/**
 * A [VerificationResult] with a counterexample.
 * @author Benjamin Alt
 */
class Counterexample(
    val specification: ConstraintSpecification,
    val counterexample: ConcreteSpecification,
    override val log: String,
) : VerificationResult() {
    /**
     * Create a new Counterexample from a given [ConcreteSpecification] and a log file.
     * @param counterexample The concrete specification (counterexample)
     * @param logFile The log file
     */
    init {
        assert(counterexample.isCounterExample)
    }
}