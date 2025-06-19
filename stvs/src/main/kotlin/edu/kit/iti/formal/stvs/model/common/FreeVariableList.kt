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
package edu.kit.iti.formal.stvs.model.common

import javafx.beans.property.SimpleListProperty
import javafx.collections.FXCollections
import javafx.collections.ObservableList
import tornadofx.getValue
import tornadofx.setValue

/**
 * A list of free variables.
 * @author Philipp
 */
class FreeVariableList {
    private val variablesProperty = SimpleListProperty<FreeVariable>(FXCollections.observableArrayList())

    /**
     * Get the [ObservableList] of free variables. This list is "deeply observable", meaning
     * that changes to the properties of the [FreeVariable]s it contains cause change events
     * on the list.
     * @return The [ObservableList] of [FreeVariable]s
     */
    var variables: ObservableList<FreeVariable> by variablesProperty

    /**
     * Construct a FreeVariableList from a list of [FreeVariable]s.
     * @param variables The list of free variables
     */
    @JvmOverloads
    constructor(variables: MutableList<FreeVariable> = arrayListOf()) {
        this.variables = FXCollections.observableList(variables, FreeVariable.EXTRACTOR)
    }

    /**
     * Copy constructor for deep copies of a [FreeVariableList].
     *
     * @param freeVariableList the list to copy
     */
    constructor(freeVariableList: FreeVariableList) {
        val clonedVariables = arrayListOf<FreeVariable>()
        for (freeVar in freeVariableList.variables) {
            clonedVariables.add(FreeVariable(freeVar))
        }
        this.variables = FXCollections.observableList(clonedVariables, FreeVariable.EXTRACTOR)
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as FreeVariableList

        return variables == other.variables
    }

    override fun hashCode(): Int = variables.hashCode()
}