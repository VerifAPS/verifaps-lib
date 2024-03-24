package edu.kit.iti.formal.stvs.model.verification

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.logic.verification.GeTeTaVerificationEngine
import edu.kit.iti.formal.stvs.logic.verification.VerificationEngine
import edu.kit.iti.formal.stvs.model.code.Code
import edu.kit.iti.formal.stvs.model.common.NullableProperty
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.util.ProcessCreationException
import javafx.beans.property.ObjectProperty
import javafx.beans.property.SimpleObjectProperty
import javafx.beans.value.ChangeListener
import javafx.beans.value.ObservableValue
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient
import tornadofx.getValue
import tornadofx.setValue
import java.io.IOException

/**
 * The main model object for orchestrating a verification. Has a reference to the currently loaded
 * [Code], uses a [VerificationEngine] from the logic package to verify it against a
 * [ConstraintSpecification] and provides access to the [VerificationResult].
 *
 * @author Benjamin Alt
 */
@Serializable
class VerificationScenario() {
    @Transient
    val verificationResultProperty = NullableProperty<VerificationResult>()
    var verificationResult by verificationResultProperty

    @Transient
    var verificationEngine: VerificationEngine? = null

    @Transient
    val codeProperty: ObjectProperty<Code> = SimpleObjectProperty(Code())
    var code by codeProperty

    @Transient
    val verificationStateProperty = SimpleObjectProperty(VerificationState.NOT_STARTED)
    val verificationState by verificationStateProperty


    @Transient
    val activeSpecProperty = NullableProperty<ConstraintSpecification?>()
    var activeSpec by activeSpecProperty


    /**
     * Constructs a VerificationScenario from a given [Code].
     *
     * @param code The initial code
     */

    /**
     * Starts a verification of the current [Code] against a given
     * [ConstraintSpecification].
     *
     * @param config The config to take into account (i.e. for verification timeouts, paths to
     * dependencies etc.)
     * @param spec The specification to be verified
     * @throws IOException Exception while IO interaction
     * @throws ExportException Exception while exporting
     * @throws ProcessCreationException exception while creating process
     */
    @Throws(IOException::class, ExportException::class, ProcessCreationException::class)
    fun verify(config: GlobalConfig, spec: ConstraintSpecification) {
        activeSpec = spec
        val ve = GeTeTaVerificationEngine(config, codeProperty.get().parsedCode!!.definedTypes)
        ve.verificationResultProperty.addListener(VerificationChangedListener())
        verificationStateProperty.value = VerificationState.RUNNING
        ve.startVerification(this, spec)

        verificationEngine = ve
    }

    /**
     * Stops a currently running verification.
     */
    fun cancel() {
        if (verificationEngine != null) {
            verificationEngine!!.cancelVerification()
        }
        verificationStateProperty.set(VerificationState.CANCELLED)
    }

    private inner class VerificationChangedListener : ChangeListener<VerificationResult?> {
        override fun changed(
            observable: ObservableValue<out VerificationResult?>?,
            oldValue: VerificationResult?,
            newValue: VerificationResult?
        ) {
            verificationResult = newValue
            verificationStateProperty.set(VerificationState.FINISHED)
        }
    }
}
