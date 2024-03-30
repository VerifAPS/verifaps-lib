package edu.kit.iti.formal.stvs.view

import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.table.HybridSpecification
import edu.kit.iti.formal.stvs.model.verification.*
import edu.kit.iti.formal.stvs.view.common.AlertFactory
import javafx.scene.control.Alert.AlertType

/**
 * Handles a verification result on the view side: Shows the appropriate dialogs depending on the
 * result type, etc.
 */
class VerificationResultHandler(private val controller: StvsRootController) : VerificationResultVisitor<Unit> {
    /**
     * Visits a [Counterexample]. This displays the counterexample in a new tab.
     *
     * @param result Counterexample to visit.
     */
    override fun visitCounterexample(result: Counterexample) {
        AlertFactory.createAlert(
            AlertType.INFORMATION, "Counterexample Available",
            "A counterexample is available.", "Complete log below", result.log
        ).showAndWait()
        val rootModel = controller.rootModel
        // Show read-only copy of spec with counterexample in a new tab
        val verifiedSpec = result.specification
        val readOnlySpec = HybridSpecification(
            ConstraintSpecification(verifiedSpec), false
        )
        readOnlySpec.counterExample = result.counterexample
        val newIndex = rootModel.hybridSpecifications.size
        rootModel.hybridSpecifications.add(newIndex, readOnlySpec)
    }

    /**
     * Visits a [VerificationError]. This displays an appropriate error dialog.
     *
     * @param result error to visit
     */
    override fun visitVerificationError(result: VerificationError) {
        val expandableContent = result.log
        System.err.println(expandableContent)
        AlertFactory.createAlert(
            AlertType.ERROR, "Verification Error",
            "An error occurred during verification.", expandableContent
        )
            .showAndWait()
    }

    /**
     * Visits a [VerificationSuccess]. This displays an appropriate success dialog.
     *
     * @param result success to visit
     */
    override fun visitVerificationSuccess(result: VerificationSuccess) {
        AlertFactory.createAlert(
            AlertType.INFORMATION, "Verification Successful",
            "The verification completed successfully.", "Verification done", result.log
        ).showAndWait()
    }

    override fun visitEmpty(verificationResult: VerificationResult) {}
}
