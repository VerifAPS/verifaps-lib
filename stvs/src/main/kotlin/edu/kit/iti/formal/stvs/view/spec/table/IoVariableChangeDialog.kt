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
package edu.kit.iti.formal.stvs.view.spec.table

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable
import javafx.scene.control.Button
import javafx.scene.control.ButtonType
import javafx.scene.control.Dialog
import javafx.util.Callback

/**
 *
 * The dialog that is opened when a user right-clicks on a column header and clicks on
 * "Change".
 *
 * @author Philipp
 */
class IoVariableChangeDialog(val variableToChange: SpecIoVariable, alreadyDefinedVariables: List<SpecIoVariable>) : Dialog<Void?>() {
    private val changeButton: ButtonType

    private val definitionPane: IoVariableDefinitionPane

    /**
     * Opens a dialog that allows to change the column header of a specification table.
     * It is impossible to set the [SpecIoVariable]s name to a name that is already used
     * inside the table.
     *
     * @param variableToChange the model to change
     * @param alreadyDefinedVariables the already defined variables for finding out whether
     * the name was changed to something illegal
     */
    init {
        title = "Change Settings of " + variableToChange!!.name
        this.changeButton = ButtonType("Change")
        this.definitionPane = IoVariableDefinitionPane(
            variableToChange.category,
            variableToChange.role,
            variableToChange.name,
            variableToChange.type,
        )

        resultConverter = Callback { buttonType: ButtonType -> this.convertResult(buttonType) }

        dialogPane.content = definitionPane
        dialogPane.buttonTypes.add(changeButton)
        val button = dialogPane.lookupButton(changeButton) as Button
        button.isDefaultButton = true
        dialogPane.id = "IoVariableChangeDialogPane"

        dialogPane.lookupButton(changeButton).disableProperty()
            .bind(definitionPane.createDefinitionInvalidBinding(alreadyDefinedVariables))
    }

    private fun convertResult(buttonType: ButtonType): Void? {
        if (buttonType == changeButton) {
            definitionPane.applyChangesToVariable(variableToChange)
        }
        return null
    }
}