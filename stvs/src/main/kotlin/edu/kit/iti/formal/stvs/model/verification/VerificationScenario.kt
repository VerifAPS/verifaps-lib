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
class VerificationScenario {
    val verificationResultProperty = NullableProperty<VerificationResult>()
    var verificationResult by verificationResultProperty

    var verificationEngine: VerificationEngine? = null

    val codeProperty: ObjectProperty<Code> = SimpleObjectProperty(Code())
    var code: Code by codeProperty

    val verificationStateProperty = SimpleObjectProperty(VerificationState.NOT_STARTED)
    val verificationState by verificationStateProperty

    val activeSpecProperty = NullableProperty<ConstraintSpecification>()
    var activeSpec: ConstraintSpecification? by activeSpecProperty

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
        val ve = GeTeTaVerificationEngine(config, codeProperty.get().parsedCode!!)
        ve.verificationResultProperty.addListener(VerificationChangedListener())
        verificationStateProperty.value = VerificationState.RUNNING
        ve.startVerification(this, ConstraintSpecification(spec))

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
            newValue: VerificationResult?,
        ) {
            verificationResult = newValue
            verificationStateProperty.set(VerificationState.FINISHED)
        }
    }
}