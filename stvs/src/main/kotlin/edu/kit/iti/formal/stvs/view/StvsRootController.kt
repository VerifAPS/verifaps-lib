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

import edu.kit.iti.formal.stvs.logic.io.ExportException
import edu.kit.iti.formal.stvs.model.StvsRootModel
import edu.kit.iti.formal.stvs.model.code.Code
import edu.kit.iti.formal.stvs.model.code.ParsedCode
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.verification.VerificationResult
import edu.kit.iti.formal.stvs.util.ProcessCreationException
import edu.kit.iti.formal.stvs.view.common.AlertFactory
import edu.kit.iti.formal.stvs.view.editor.EditorPaneController
import edu.kit.iti.formal.stvs.view.spec.SpecificationsPaneController
import edu.kit.iti.formal.stvs.view.spec.VerificationEvent
import javafx.beans.property.ListProperty
import javafx.beans.property.SimpleListProperty
import javafx.collections.FXCollections
import javafx.scene.control.Alert.AlertType
import java.io.IOException

/**
 * The root controller. Manages the largest-scale view of the application (see
 * [StvsRootView]).
 * @author Carsten Csiky
 */
class StvsRootController(
    /**
     * Get the current [StvsRootModel] managed by this controller.
     * @return The root model
     */
    val rootModel: StvsRootModel,
) : Controller {
    override val view: StvsRootView

    private val types: ListProperty<Type>
    private val ioVars: ListProperty<CodeIoVariable>
    private val specificationsPaneController: SpecificationsPaneController
    private val verificationResultHandler: VerificationResultHandler
    private var editorPaneController: EditorPaneController

    /**
     * Controller for the [StvsRootView].
     * Here the main distinction between specification code and menu is made.
     * @param rootModel model to represent
     */
    init {
        this.editorPaneController = EditorPaneController(
            rootModel.scenario.code,
            rootModel.globalConfig,
        )

        this.types =
            SimpleListProperty(FXCollections.observableArrayList(typesFromCode(rootModel.scenario.code.parsedCode)))

        this.ioVars =
            SimpleListProperty(FXCollections.observableArrayList(ioVarsFromCode(rootModel.scenario.code.parsedCode)))

        this.specificationsPaneController = SpecificationsPaneController(
            rootModel.hybridSpecifications,
            rootModel.scenario.verificationStateProperty,
            types,
            ioVars,
            rootModel.globalConfig,
            rootModel.scenario,
        )

        rootModel.scenario.codeProperty
            .addListener { _, _, code -> this.onCodeChange(code) }
        rootModel.scenario.code.parsedCodeProperty
            .addListener { _, _, parsedCode -> onParsedCodeChange(parsedCode) }
        rootModel.scenario.verificationResultProperty
            .addListener { _, _, res -> this.onVerificationResultChange(res) }

        this.view = StvsRootView(editorPaneController.view, specificationsPaneController.view)
        this.verificationResultHandler = VerificationResultHandler(this)
        view.addEventHandler(VerificationEvent.Companion.EVENT_TYPE) { event: VerificationEvent ->
            this.onVerificationEvent(
                event,
            )
        }
    }

    /**
     * Handles verification events (triggers start or cancel of verification depending on the event
     * type).
     *
     * @param event The verification event
     */
    private fun onVerificationEvent(event: VerificationEvent) {
        when (event.type) {
            VerificationEvent.Type.START -> try {
                rootModel.scenario.verify(rootModel.globalConfig, event.constraintSpec)
            } catch (e: ExportException) {
                AlertFactory.createAlert(e, "Verification Error", "The verification " + "could not be started.")
                    .showAndWait()
                rootModel.scenario.cancel()
            } catch (e: IOException) {
                AlertFactory.createAlert(e, "Verification Error", "The verification " + "could not be started.")
                    .showAndWait()
                rootModel.scenario.cancel()
            } catch (e: ProcessCreationException) {
                AlertFactory.createAlert(e, "Verification Error", "The verification " + "could not be started.")
                    .showAndWait()
                rootModel.scenario.cancel()
            }

            VerificationEvent.Type.STOP -> {
                rootModel.scenario.cancel()
                AlertFactory.createAlert(
                    AlertType.INFORMATION,
                    "Verification cancelled",
                    "Verification cancelled.",
                    "",
                ).showAndWait()
            }

            else -> throw IllegalStateException("Could not handle verification event type.")
        }
    }

    private fun ioVarsFromCode(parsedCode: ParsedCode?): List<CodeIoVariable?> {
        if (parsedCode == null) {
            return emptyList<CodeIoVariable>()
        }
        return parsedCode.definedVariables
    }

    private fun typesFromCode(parsedCode: ParsedCode?): List<Type> {
        if (parsedCode == null) {
            return listOf(TypeInt, TypeBool)
        }
        return parsedCode.definedTypes
    }

    /**
     * Change handler for the code. Updates the editor on code changes.
     *
     * @param observableValue The observable value
     * @param old The code before the change
     * @param code The code after the change
     */
    private fun onCodeChange(code: Code) {
        editorPaneController = EditorPaneController(code, rootModel.globalConfig)
        code.parsedCodeProperty
            .addListener { _, _, parsedCode: ParsedCode? -> onParsedCodeChange(parsedCode) }
        view.editor = editorPaneController.view
        onParsedCodeChange(code.parsedCodeProperty.get())
    }

    private fun onParsedCodeChange(parsedCode: ParsedCode?) {
        if (parsedCode != null) {
            types.setAll(typesFromCode(parsedCode))
            ioVars.setAll(ioVarsFromCode(parsedCode))
        }
    }

    /**
     * Change handler for the verification result. Informs the user about the result of a verification
     * and opens counterexamples in a new tab, if a counterexample is available.
     *
     * @param o The observable value
     * @param old The verification result before the change
     * @param res The verification result after the change
     */
    private fun onVerificationResultChange(res: VerificationResult?) {
        res?.accept(verificationResultHandler)
            ?: AlertFactory.createAlert(
                AlertType.ERROR,
                "Verification Error",
                "The verification result is null.",
                "",
            ).showAndWait()
    }
}