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
package edu.kit.iti.formal.stvs.model.table

import com.google.common.truth.Truth
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator
import javafx.beans.property.SimpleListProperty
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.CsvSource
import tornadofx.asObservable

/**
 * @author Benjamin Alt
 * @author Philipp
 */
class ConstraintSpecificationValidatorTest {

    @ParameterizedTest
    @CsvSource(
        textBlock = """
        valid_table.json
        invalid_cell_type.json
        unknown_cell_variable.json
        unknown_iovar.json
        invalid_iovar_type.json
        invalid_cell_grammar.json
        unsupported_cell_grammar.json
        invalid_duration_grammar.json""",
    )
    fun testProblems(testfile: String) {
        val testJson = JsonTableParser.jsonFromResource(testfile, ConstraintSpecificationValidatorTest::class.java)
        val codeIoVariables = JsonTableParser.codeIoVariablesFromJson(testJson).asObservable()
        val typeContext = listOf(TypeInt, TypeBool).asObservable()
        val freeVars = JsonTableParser.freeVariableSetFromJson(testJson)

        val testSpec = JsonTableParser.constraintTableFromJson(testJson)
        val validator = FreeVariableListValidator(
            SimpleListProperty(typeContext),
            freeVars,
        )

        val recognizer = ConstraintSpecificationValidator(
            SimpleListProperty(typeContext),
            SimpleListProperty(codeIoVariables),
            validator.validFreeVariablesProperty,
            testSpec,
        )

        val expectedProblems = JsonTableParser.expectedSpecProblemsFromJson(testJson)

        val exp = expectedProblems.map { it.simpleName }.toSortedSet()
        val act = recognizer.problems.map { it.javaClass.simpleName }.toSortedSet()

        Truth.assertThat(act).isEqualTo(exp)
    }
}