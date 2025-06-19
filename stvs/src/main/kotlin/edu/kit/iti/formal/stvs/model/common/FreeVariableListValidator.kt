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

import edu.kit.iti.formal.stvs.model.expressions.Type
import javafx.beans.Observable
import javafx.beans.property.*
import javafx.collections.FXCollections
import javafx.collections.ObservableList
import tornadofx.getValue
import tornadofx.setValue

/**
 * The validator for the effective model [FreeVariableList]. This class provides
 * automatically updating properties for the formal model
 * (see [.validFreeVariablesProperty]) and for any
 * problems encountered while validating (see [.problemsProperty]).
 *
 * @author Philipp
 */
class FreeVariableListValidator(
    private val typeContext: ListProperty<Type>,
    private val freeVariables: FreeVariableList,
) {
    val problemsProperty =
        SimpleMapProperty<FreeVariable, MutableList<FreeVariableProblem>>(FXCollections.observableHashMap())
    var problems by problemsProperty

    val validFreeVariablesProperty = SimpleListProperty(FXCollections.observableArrayList<ValidFreeVariable>())
    val validFreeVariables: ObservableList<ValidFreeVariable> by validFreeVariablesProperty

    val validProperty: BooleanProperty = SimpleBooleanProperty(false)
    var valid by validProperty

    /**
     * Creates a validator with the given formal type context model for the effective
     * free variable model.
     *
     * @param typeContext the context for validating the free variables and generating the valid
     * free variables
     * @param freeVariables the free variables model to validate
     */
    init {
        freeVariables.variables.addListener { _: Observable? -> revalidate() }
        typeContext.addListener { _: Observable? -> revalidate() }
        revalidate()
    }

    /**
     * Starts the validation algorithm and updates the [validFreeVariablesProperty] and
     * the [problemsProperty].
     */
    fun revalidate() {
        val typesByName = typeContext.get().associateBy { obj -> obj.typeName }
        val variableMap = freeVariables.variables.associate {
            val type = typesByName[it.type]
            if (type == null) {
                addProblem(it, InvalidFreeVariableProblem("Type ${it.type} is unknown"))
                return
            }
            it.name to type
        }

        val validated = arrayListOf<ValidFreeVariable>()

        freeVariables.variables.forEach { freeVariable: FreeVariable ->
            val problem = DuplicateFreeVariableProblem.checkForDuplicates(
                freeVariable,
                freeVariables.variables,
            )
            if (problem == null) {
                try {
                    validated.add(
                        InvalidFreeVariableProblem.tryToConvertToValid(freeVariable, typesByName, variableMap),
                    )
                } catch (problem: InvalidFreeVariableProblem) {
                    addProblem(freeVariable, problem)
                }
            } else {
                addProblem(freeVariable, problem)
            }
        }

        validFreeVariablesProperty.setAll(validated)
        validProperty.set(problems.isEmpty())
    }

    private fun addProblem(freeVariable: FreeVariable, problem: FreeVariableProblem) =
        problems.computeIfAbsent(freeVariable) { arrayListOf() }.add(problem)
}