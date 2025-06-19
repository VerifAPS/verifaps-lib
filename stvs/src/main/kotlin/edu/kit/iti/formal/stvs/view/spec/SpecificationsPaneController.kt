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

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.common.FreeVariableList
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.table.HybridSpecification
import edu.kit.iti.formal.stvs.model.verification.VerificationScenario
import edu.kit.iti.formal.stvs.model.verification.VerificationState
import edu.kit.iti.formal.stvs.view.Controller
import javafx.beans.binding.Bindings
import javafx.beans.property.ListProperty
import javafx.beans.property.ObjectProperty
import javafx.collections.ListChangeListener
import javafx.collections.ObservableList
import javafx.event.ActionEvent
import javafx.event.Event
import javafx.event.EventHandler
import javafx.scene.control.ContextMenu
import javafx.scene.control.MenuItem
import javafx.scene.control.Tab
import javafx.scene.control.TextInputDialog
import org.kordamp.ikonli.fontawesome5.FontAwesomeSolid
import org.kordamp.ikonli.javafx.FontIcon

/**
 * Controller for [SpecificationsPane]. The tab logic is handled here.
 *
 * @author Carsten Csiky
 */
class SpecificationsPaneController(
    private val hybridSpecifications: ObservableList<HybridSpecification>,
    private val state: ObjectProperty<VerificationState?>,
    private val typeContext: ListProperty<Type>,
    private val ioVariables: ListProperty<CodeIoVariable>,
    private val globalConfig: GlobalConfig,
    private val scenario: VerificationScenario,
) : Controller {
    override val view: SpecificationsPane = SpecificationsPane()
    private val controllers: MutableMap<Tab?, SpecificationController> = HashMap()

    /**
     * Creates an instance of this controller.
     *
     * @param hybridSpecifications list of the specifications t display
     * @param state the state of the verification
     * @param typeContext  available types in code
     * @param ioVariables  available variables in code
     * @param globalConfig Global config object
     * @param scenario scenario that represents what the verification needs
     */
    init {
        hybridSpecifications.forEach { this.addTab(it) }
        view.onTabAdded {
            val hybridSpecification =
                HybridSpecification(FreeVariableList(ArrayList()), true)
            println(ioVariables.get())
            for (ioVariable in ioVariables.get()!!) {
                val specIoVariable = SpecIoVariable(
                    category = ioVariable!!.category,
                    typeIdentifier = ioVariable.type,
                    name = ioVariable.name,
                )
                hybridSpecification.columnHeaders.add(specIoVariable)
            }
            hybridSpecifications.add(hybridSpecification)
        }

        view.tabPane.selectionModel.selectedItemProperty().addListener { _, _, tab: Tab -> onSwitchActiveTab(tab) }
        onSwitchActiveTab(view.tabPane.selectionModel.selectedItem)

        hybridSpecifications.addListener { change: ListChangeListener.Change<out HybridSpecification> ->
            while (change.next()) {
                /* addedPositionIndex stores the index that changed (starting at .getFrom()
                 * and should be ending at .getTo() ). Since in our case only one change should occur
                 * at a time, there is no need to worry about edge-cases (for now)*/
                var addedPositionIndex = change.from
                for (addItem in change.addedSubList) {
                    addTab(addItem, addedPositionIndex)
                    addedPositionIndex++
                }
                for (spec in change.removed) {
                    removeTab(change.from)
                }
            }
        }
    }

    private fun onTabCloseRequest(event: Event, tab: Tab) {
        val indexToDelete = view.tabPane.tabs.indexOf(tab)
        if (indexToDelete < 0) {
            return
        }
        hybridSpecifications.removeAt(indexToDelete)
    }

    private fun onSwitchActiveTab(tab: Tab?) {
        val controller = controllers[tab]
        if (controller == null) {
            scenario.activeSpec = null
        } else {
            scenario.activeSpec = controller.spec
        }
    }

    private fun addTab(hybridSpecification: HybridSpecification, index: Int): SpecificationController {
        val controller =
            SpecificationController(
                typeContext,
                ioVariables,
                hybridSpecification,
                this.state,
                Bindings.isEmpty(scenario.code.syntaxErrorsProperty).not(),
                globalConfig,
            )
        val tab = Tab()
        tab.onCloseRequest = EventHandler { e: Event -> onTabCloseRequest(e, tab) }
        if (hybridSpecification.isEditable) {
            tab.contextMenu = createTabContextMenu()
        }
        tab.textProperty().bind(hybridSpecification.nameProperty)
        tab.content = controller.view
        if (hybridSpecification.isEditable) {
            tab.graphic = FontIcon(FontAwesomeSolid.EDIT)
        } else {
            tab.graphic = FontIcon(FontAwesomeSolid.LOCK)
        }
        view.tabs.add(index, tab)
        controllers[tab] = controller
        view.tabPane.selectionModel.select(tab)
        scenario.activeSpec = hybridSpecification
        return controller
    }

    fun addTab(hybridSpecification: HybridSpecification): SpecificationController = addTab(hybridSpecification, 0)

    private fun onTabSetName(actionEvent: ActionEvent) {
        val activeTab = view.tabPane.selectionModel.selectedItem
        val activeSpec = controllers[activeTab]?.spec
        val textInputDialog = TextInputDialog(activeSpec!!.name)
        textInputDialog.headerText = "Set Specification Name"
        textInputDialog.title = "Specification Name"
        textInputDialog.showAndWait()
        if (textInputDialog.result != null) {
            activeSpec.name = textInputDialog.result
        }
    }

    private fun createTabContextMenu(): ContextMenu {
        val contextMenu = ContextMenu()
        val setNameItem = MenuItem("Rename")
        setNameItem.onAction = EventHandler { actionEvent: ActionEvent -> this.onTabSetName(actionEvent) }
        contextMenu.items.add(setNameItem)
        return contextMenu
    }

    private fun removeTab(index: Int) {
        val removeTab = view.tabs[index]
        controllers.remove(removeTab)
        view.tabs.removeAt(index)
    }
}