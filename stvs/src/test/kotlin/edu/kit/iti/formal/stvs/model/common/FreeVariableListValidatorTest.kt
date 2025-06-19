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

import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import javafx.beans.property.SimpleListProperty
import javafx.collections.FXCollections
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.MethodSource

/**
 * Created by philipp on 09.02.17.
 */
class FreeVariableListValidatorTest {
//    var expectedProblem: String? = null
//    var variables: List<FreeVariable?>? = null

    @ParameterizedTest
    @MethodSource("parameters")
    fun testRevalidate(expectedProblem: String, variables: List<FreeVariable>) {
        val typeContext = SimpleListProperty(
            FXCollections.observableArrayList(TypeInt, TypeBool),
        )
        val validator = FreeVariableListValidator(typeContext, FreeVariableList(variables.toMutableList()))
        checkProblems(expectedProblem, variables, validator)
    }

    private fun checkProblems(
        expectedProblem: String,
        variables: List<FreeVariable>,
        validator: FreeVariableListValidator,
    ) {
        if (expectedProblem.isEmpty()) {
            validator.problemsProperty.get().values.forEach(System.out::println)
            Assertions.assertEquals(
                variables.size,
                validator.validFreeVariablesProperty.get().size,
                "Number of valid free variables should be equal to number of unvalidated",
            )
        } else {
            val actualProblems =
                validator.problemsProperty.get().values.flatten()
            checkExpectedProblems(expectedProblem, actualProblems)
        }
    }

    private fun checkExpectedProblems(expectedProblem: String, problems: Collection<FreeVariableProblem>) {
        println("Expected problem: $expectedProblem")
        println("Actual problems: " + problems.map { (it.javaClass.simpleName + "(" + it.errorMessage + ")") })
        Assertions.assertTrue(
            problems.all { it.javaClass.simpleName == expectedProblem },
            "Problems contain only expected problems",
        )
    }

    companion object {
        @JvmStatic
        fun parameters(): List<Arguments> = listOf(
            Arguments.of("", listOf(FreeVariable("a", "INT"), FreeVariable("b", "BOOL"))),
            Arguments.of(
                "InvalidFreeVariableProblem",
                listOf(FreeVariable("a xy _%", "INT"), FreeVariable("b", "BOOL")),
            ),
            Arguments.of(
                "InvalidFreeVariableProblem",
                listOf(FreeVariable("a", "INT"), FreeVariable("b", "BOOLEAN")),
            ),
            Arguments.of(
                "InvalidFreeVariableProblem",
                listOf(FreeVariable("a", "INT", "asf"), FreeVariable("b", "BOOL")),
            ),
            Arguments.of(
                "InvalidFreeVariableProblem",
                listOf(FreeVariable("a", "INT", "TRUE"), FreeVariable("b", "BOOL")),
            ),
            Arguments.of("", listOf(FreeVariable("a", "INT", "1"), FreeVariable("b", "BOOL", "TRUE"))),
            Arguments.of(
                "DuplicateFreeVariableProblem",
                listOf(FreeVariable("my_variable", "INT"), FreeVariable("my_variable", "BOOL")),
            ),
        )
    }
}