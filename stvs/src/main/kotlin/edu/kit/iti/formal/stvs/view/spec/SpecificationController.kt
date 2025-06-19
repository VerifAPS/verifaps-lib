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
package edu.kit.iti.formal.stvs.view.spec

import edu.kit.iti.formal.stvs.logic.specification.SpecificationConcretizer
import edu.kit.iti.formal.stvs.logic.specification.smtlib.SmtConcretizer
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.common.Selection
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification
import edu.kit.iti.formal.stvs.model.table.HybridSpecification
import edu.kit.iti.formal.stvs.model.table.ValidSpecification
import edu.kit.iti.formal.stvs.model.verification.VerificationState
import edu.kit.iti.formal.stvs.util.AsyncRunner
import edu.kit.iti.formal.stvs.util.AsyncTaskCompletedHandler
import edu.kit.iti.formal.stvs.util.JavaFxAsyncTask
import edu.kit.iti.formal.stvs.view.Controller
import edu.kit.iti.formal.stvs.view.common.AlertFactory
import edu.kit.iti.formal.stvs.view.spec.table.SpecificationTableController
import edu.kit.iti.formal.stvs.view.spec.timingdiagram.TimingDiagramCollectionController
import edu.kit.iti.formal.stvs.view.spec.variables.VariableCollectionController
import javafx.beans.binding.BooleanBinding
import javafx.beans.property.BooleanProperty
import javafx.beans.property.ListProperty
import javafx.beans.property.ObjectProperty
import javafx.beans.property.SimpleBooleanProperty
import javafx.beans.value.ObservableValue
import javafx.collections.ListChangeListener
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.control.Alert
import javafx.scene.control.MenuItem

/**
 * This is the controller for the [SpecificationView]. It handles most of the view logic that
 * is invoked by verification/concretizer results.
 *
 * @author Carsten Csiky
 */
class SpecificationController(
    typeContext: ListProperty<Type>,
    codeIoVariables: ListProperty<CodeIoVariable>,
    val spec: HybridSpecification,
    stateProperty: ObjectProperty<VerificationState?>,
    codeInvalid: BooleanBinding?,
    globalConfig: GlobalConfig,
) : Controller {
    private val globalConfig: GlobalConfig
    private val concretizationHandler: ConcretizationTaskHandler
    private val stateProperty: ObjectProperty<VerificationState?>
    override val view: SpecificationView
    private val variableCollectionController: VariableCollectionController
    private val tableController: SpecificationTableController
    private var timingDiagramCollectionController: TimingDiagramCollectionController? = null
    private val selection: Selection?
    private val specificationInvalid: BooleanProperty
    private val specificationConcretizable: BooleanProperty
    private var concretizingTask: JavaFxAsyncTask<ConcreteSpecification>? = null

    /**
     * This creates an instance of the controller.
     *
     * @param typeContext available types in code
     * @param codeIoVariables available variables in code
     * @param hybridSpecification specification that should be represented by this controller
     * @param stateProperty the state of the verification
     * @param codeInvalid Tells if the code is valid
     * @param globalConfig Global config object
     */
    init {
        this.stateProperty = stateProperty
        this.stateProperty.addListener { observableValue, oldState: VerificationState?, newState: VerificationState? ->
            this.onVerificationStateChanged(observableValue, oldState, newState)
        }
        this.view = SpecificationView()
        this.selection = spec.getSelection()
        this.globalConfig = globalConfig
        this.variableCollectionController = VariableCollectionController(typeContext, spec.freeVariableList)
        this.tableController = SpecificationTableController(
            globalConfig,
            typeContext,
            codeIoVariables,
            variableCollectionController.validator.validFreeVariablesProperty,
            spec,
        )
        this.specificationInvalid = SimpleBooleanProperty(true)
        specificationInvalid.bind(
            variableCollectionController.validator.validProperty.not()
                .or(tableController.validator.validProperty.not()).or(codeInvalid),
        )
        this.specificationConcretizable = SimpleBooleanProperty(true)
        specificationConcretizable
            .bind(tableController.validator.validSpecificationProperty.isNotNull())
        this.concretizationHandler = ConcretizationTaskHandler()

        // use event trigger to generate timing-diagram, to minimize code-duplication
        onConcreteInstanceChanged(concreteSpecification)

        view.variableCollection = variableCollectionController.view
        view.variableCollection!!.freeVariableTableView.isEditable = spec.isEditable
        val freeVarMenuItems: List<MenuItem> =
            view.variableCollection!!.freeVariableTableView.contextMenu.items
        for (menuItem in freeVarMenuItems) {
            menuItem.isDisable = !spec.isEditable
        }
        view.setTable(tableController.view)
        view.startButton.onAction =
            EventHandler { actionEvent: ActionEvent -> this.onVerificationButtonClicked(actionEvent) }
        view.startButton.disableProperty().bind(specificationInvalid)
        view.startConcretizerButton.disableProperty().bind(specificationConcretizable.not())
        view.startConcretizerButton.onAction =
            EventHandler { actionEvent: ActionEvent -> this.startConcretizer(actionEvent) }

        spec.concreteInstanceProperty
            .addListener {
                    observable: ObservableValue<out ConcreteSpecification?>?,
                    old: ConcreteSpecification?,
                    newVal: ConcreteSpecification?,
                ->
                this.onConcreteInstanceChanged(
                    newVal,
                )
            }
        registerTimingDiagramDeactivationHandler()
    }

    private fun onVerificationStateChanged(
        observableValue: ObservableValue<out VerificationState?>,
        oldState: VerificationState?,
        newState: VerificationState?,
    ) {
        when (newState) {
            VerificationState.RUNNING -> view.setVerificationButtonStop()
            else -> view.setVerificationButtonPlay()
        }
    }

    private fun registerTimingDiagramDeactivationHandler() {
        spec.durations.addListener(ListChangeListener { change -> this.specChanged(change) })
        spec.columnHeaders
            .addListener(ListChangeListener { change -> this.specChanged(change) })
        spec.rows.addListener(ListChangeListener { change -> this.specChanged(change) })
        spec.freeVariableList.variables
            .addListener(ListChangeListener { change -> this.specChanged(change) })
        spec.concreteInstance = null
    }

    private fun specChanged(change: ListChangeListener.Change<*>) {
        if (timingDiagramCollectionController != null) {
            timingDiagramCollectionController!!.activated = false
        }
    }

    private fun onConcreteInstanceChanged(newVal: ConcreteSpecification?) {
        if (concreteSpecification == null) {
            view.setEmptyDiagram()
        } else {
            this.timingDiagramCollectionController = TimingDiagramCollectionController(concreteSpecification, selection)
            view.diagram = timingDiagramCollectionController!!.view
        }
    }

    private fun onConcretizationActive() {
        view.setConcretizerButtonStop()
        view.startConcretizerButton.onAction =
            EventHandler { actionEvent: ActionEvent -> this.stopConcretizer() }
    }

    private fun onConcretizationInactive() {
        view.setConcretizerButtonStart()
        view.startConcretizerButton.onAction =
            EventHandler { actionEvent: ActionEvent -> this.startConcretizer(actionEvent) }
    }

    private fun startConcretizer(actionEvent: ActionEvent) {
        val runner = ConcretizationRunner(
            tableController.validator.validSpecification!!,
            variableCollectionController.validator.validFreeVariables,
        )
        val task = JavaFxAsyncTask(
            globalConfig.simulationTimeout,
            runner,
            this.concretizationHandler,
        )

        this.concretizingTask = task
        concretizingTask!!.start()

        onConcretizationActive()
    }

    private fun stopConcretizer() {
        if (concretizingTask != null) {
            concretizingTask!!.terminate()
            concretizingTask = null
        }
        onConcretizationInactive()
    }

    private val concreteSpecification: ConcreteSpecification?
        get() = spec.counterExample ?: spec.concreteInstance

    private fun onVerificationButtonClicked(actionEvent: ActionEvent) {
        when (stateProperty.get()) {
            VerificationState.RUNNING -> view.onVerificationButtonClicked(spec, VerificationEvent.Type.STOP)
            else -> view.onVerificationButtonClicked(spec, VerificationEvent.Type.START)
        }
    }

    private inner class ConcretizationTaskHandler : AsyncTaskCompletedHandler<ConcreteSpecification> {
        override fun onSuccess(concreteSpec: ConcreteSpecification) {
            spec.concreteInstance = concreteSpec
            timingDiagramCollectionController!!.activated = true
            onConcretizationInactive()
        }

        override fun onException(exception: Exception?) {
            val alert: Alert = AlertFactory.createAlert(exception!!)
            alert.showAndWait()
            onConcretizationInactive()
        }
    }

    private inner class ConcretizationRunner(
        val specToConcretize: ValidSpecification,
        val freeVariables: List<ValidFreeVariable>,
    ) : AsyncRunner<ConcreteSpecification> {
        val concretizer: SpecificationConcretizer = SmtConcretizer(globalConfig)

        @Throws(Exception::class)
        override fun run(): ConcreteSpecification =
            concretizer.calculateConcreteSpecification(specToConcretize, freeVariables)!!

        override fun terminate() {
            concretizer.terminate()
        }
    }
}