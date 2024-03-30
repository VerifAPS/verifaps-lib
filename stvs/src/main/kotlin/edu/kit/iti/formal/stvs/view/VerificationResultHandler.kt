package edu.kit.iti.formal.stvs.view

import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.table.HybridSpecification
import edu.kit.iti.formal.stvs.model.verification.*
import edu.kit.iti.formal.stvs.view.common.AlertFactory
import javafx.scene.control.Alert.AlertType
import org.apache.commons.io.FileUtils
import java.io.IOException

/**
 * Handles a verification result on the view side: Shows the appropriate dialogs depending on the
 * result type, etc.
 */
class VerificationResultHandler(private val controller: StvsRootController) : VerificationResultVisitor {
    private var logFileContents = ""
    private var alertBody = "Verification done."

    /**
     * Visits a [Counterexample]. This displays the counterexample in a new tab.
     *
     * @param result Counterexample to visit.
     */
    override fun visitCounterexample(result: Counterexample?) {
        makeAlertBody(result)
        AlertFactory.createAlert(
            AlertType.INFORMATION, "Counterexample Available",
            "A counterexample is available.", alertBody, logFileContents
        ).showAndWait()
        val rootModel = controller.rootModel
        // Show read-only copy of spec with counterexample in a new tab
        val verifiedSpec = rootModel.scenario.verificationEngine?.verificationSpecification
        val readOnlySpec = HybridSpecification(
            ConstraintSpecification(verifiedSpec!!), false
        )
        readOnlySpec.counterExample = result!!.counterexample
        val newIndex = rootModel.hybridSpecifications.size
        rootModel.hybridSpecifications.add(newIndex, readOnlySpec)
    }

    /**
     * Visits a [VerificationError]. This displays an appropriate error dialog.
     *
     * @param result error to visit
     */
    override fun visitVerificationError(result: VerificationError?) {
        var expandableContent: String? = ""
        if (result!!.logFile != null) {
            try {
                expandableContent = FileUtils.readFileToString(result.logFile, "utf-8")
            } catch (ex: IOException) {
                // Do nothing, don't want to distract from the actual error
            }
        }
        System.err.println(expandableContent)
        AlertFactory.createAlert(
            AlertType.ERROR, "Verification Error",
            "An error occurred during verification.", result.message /*
            stacktrace should not be shown. (See Issue #20)
            expandableContent*/
        )
            .showAndWait()
    }

    /**
     * Visits a [VerificationSuccess]. This displays an appropriate success dialog.
     *
     * @param result success to visit
     */
    override fun visitVerificationSuccess(result: VerificationSuccess?) {
        makeAlertBody(result)
        AlertFactory.createAlert(
            AlertType.INFORMATION, "Verification Successful",
            "The verification completed successfully.", alertBody, logFileContents
        ).showAndWait()
    }

    private fun makeAlertBody(result: VerificationResult?) {
        if (result!!.logFile != null) {
            alertBody = " See the log at " + result.logFile!!.absolutePath + "."
            try {
                logFileContents = FileUtils.readFileToString(result.logFile, "utf-8")
            } catch (ex: IOException) {
                // Do nothing, don't want to distract from the result
            }
        }
    }
}
