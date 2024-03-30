package edu.kit.iti.formal.stvs.logic.verification

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.verification.VerificationResult
import edu.kit.iti.formal.stvs.model.verification.VerificationResultEmpty
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario
import edu.kit.iti.formal.stvs.util.ProcessCreationException
import javafx.beans.property.SimpleObjectProperty
import tornadofx.getValue
import java.io.IOException

/**
 * Strategy for verification of the VerificationScenario.
 *
 * @author Benjamin Alt
 */
abstract class VerificationEngine {
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
    abstract fun startVerification(scenario: VerificationScenario, spec: ConstraintSpecification)

    val verificationResultProperty = SimpleObjectProperty<VerificationResult>(VerificationResultEmpty)
    val verificationResult: VerificationResult by verificationResultProperty

    /**
     * Cancels a running verification.
     */
    abstract fun cancelVerification()

}
