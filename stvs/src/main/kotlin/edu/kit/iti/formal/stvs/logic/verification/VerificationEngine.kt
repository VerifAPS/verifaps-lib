package edu.kit.iti.formal.stvs.logic.verification

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.model.common.NullableProperty
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.verification.VerificationResult
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario
import edu.kit.iti.formal.stvs.util.ProcessCreationException
import java.io.IOException

/**
 * Strategy for verification of the VerificationScenario.
 *
 * @author Benjamin Alt
 */
interface VerificationEngine {
    /**
     * Starts a verification in its own thread.
     *
     * @param scenario scenario that hold the code to be checked
     * @param spec specification that should be checked
     * @throws IOException exception while creating process
     * @throws ExportException exception while exporting
     * @throws ProcessCreationException exception while creating a process for verification
     */
    @Throws(IOException::class, ExportException::class, ProcessCreationException::class)
    fun startVerification(scenario: VerificationScenario, spec: ConstraintSpecification)

    val verificationResultProperty: NullableProperty<VerificationResult?>
    val verificationResult: VerificationResult?
        get() = verificationResultProperty.get()

    /**
     * Get the last specification for which a verification was triggered.
     * This value is null before any calls of
     * [.startVerification], but will never
     * be null once that method is called once.
     *
     * @return The last specification for which a verification was triggered
     */
    val verificationSpecification: ConstraintSpecification?

    /**
     * Cancels a running verification.
     */
    fun cancelVerification()
}
