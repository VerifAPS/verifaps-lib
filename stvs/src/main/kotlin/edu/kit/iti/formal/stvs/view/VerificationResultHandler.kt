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
            AlertType.INFORMATION,
            "Counterexample Available",
            "A counterexample is available.",
            "Complete log below",
            result.log,
        ).showAndWait()
        val rootModel = controller.rootModel
        // Show read-only copy of spec with counterexample in a new tab
        val verifiedSpec = result.specification
        val readOnlySpec = HybridSpecification(
            ConstraintSpecification(verifiedSpec),
            false,
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
            AlertType.ERROR,
            "Verification Error",
            "An error occurred during verification.",
            expandableContent,
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
            AlertType.INFORMATION,
            "Verification Successful",
            "The verification completed successfully.",
            "Verification done",
            result.log,
        ).showAndWait()
    }

    override fun visitEmpty(verificationResult: VerificationResult) {}
}