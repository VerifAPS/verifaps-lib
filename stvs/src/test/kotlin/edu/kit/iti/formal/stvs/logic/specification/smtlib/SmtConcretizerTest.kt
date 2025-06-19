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
package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.stvs.TestUtils
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable
import edu.kit.iti.formal.stvs.model.config.GlobalConfig.Companion.autoloadConfig
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import edu.kit.iti.formal.stvs.model.table.ValidSpecification
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator
import javafx.beans.property.SimpleListProperty
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import tornadofx.asObservable
import java.util.*

/**
 * Created by csicar on 13.02.17.
 */
class SmtConcretizerTest {
    private var freeVariables: List<ValidFreeVariable>? = null

    private fun importSpec(name: String): ValidSpecification {
        val typeContext = listOf(
            TypeInt,
            TypeBool,
            TypeEnum(
                "colors",
                mutableListOf("red", "green", "blue"),
            ),
        )
        val codeIoVariables: List<CodeIoVariable> = LinkedList()

        val constraintSpec: ConstraintSpecification =
            ImporterFacade.importConstraintSpec(javaClass.getResourceAsStream(name)!!)
        val tc = SimpleListProperty(typeContext.asObservable())
        val freeVariableListValidator = FreeVariableListValidator(tc, constraintSpec.freeVariableList)
        val freeVariables: List<ValidFreeVariable> = freeVariableListValidator.validFreeVariables
        this.freeVariables = freeVariables
        val validator = ConstraintSpecificationValidator(
            tc,
            SimpleListProperty(codeIoVariables.asObservable()),
            freeVariables.asObservable(),
            constraintSpec,
        )
        validator.problems.map { it?.errorMessage }.forEach { println(it) }
        return validator.validSpecification!!
    }

    @BeforeEach
    fun before() {
        TestUtils.assumeZ3Exists()
    }

    @Test
    fun testTermination() {
        val spec = importSpec("testSpec.xml")
        val maxDurations = mapOf(0 to 3000, 1 to 1, 2 to 2)
        val concretizer = SmtConcretizer(autoloadConfig())
        concretizer.calculateConcreteSpecification(spec, freeVariables!!)
        val start = System.currentTimeMillis()
        concretizer.terminate()
        val end = System.currentTimeMillis()
        val maxTime: Long = 5
        Assertions.assertTrue(
            end - start < maxTime,
            "Except time to terminate to be smaller than " + maxTime + ", but was" + (end - start),
        )
    }

    @Test
    fun simpleTest() {
        val spec = importSpec("testSpec.xml")
        val maxDurations = mapOf(0 to 7, 1 to 1, 2 to 2)
        val concretizer = SmtConcretizer(autoloadConfig())
        concretizer.calculateConcreteSpecification(spec, freeVariables!!)
    }
}