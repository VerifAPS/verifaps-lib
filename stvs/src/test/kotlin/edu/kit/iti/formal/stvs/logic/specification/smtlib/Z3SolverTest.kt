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
import edu.kit.iti.formal.stvs.logic.specification.ConcretizationException
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
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test
import tornadofx.asObservable
import java.util.*

/**
 * Created by leonk on 09.02.2017.
 */
class Z3SolverTest {
    private var freeVariables: List<ValidFreeVariable> = listOf()
    private var solver = Z3Solver(autoloadConfig()).also {
        TestUtils.assumeZ3Exists()
    }

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

        val constraintSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(
            javaClass.getResourceAsStream(name)!!,
        )
        val freeVariableListValidator = FreeVariableListValidator(
            SimpleListProperty(typeContext.asObservable()),
            constraintSpec.freeVariableList,
        )
        val freeVariables: List<ValidFreeVariable> = freeVariableListValidator.validFreeVariablesProperty.get()
        this.freeVariables = freeVariables
        val recognizer = ConstraintSpecificationValidator(
            SimpleListProperty(typeContext.asObservable()),
            SimpleListProperty(codeIoVariables.asObservable()),
            (freeVariables).asObservable(),
            constraintSpec,
        )
        val specProblems = recognizer.problemsProperty.get()
        specProblems.map { it?.errorMessage }.forEach { System.err.println(it) }

        return recognizer.validSpecification!!
    }

    @Test
    @Tag("performance")
    @Throws(Exception::class)
    fun testLongExample() {
        val config = autoloadConfig()
        val solver = Z3Solver(config)
        val spec = importSpec("spec_long_single_variable_example.xml")
        val encoder = SmtEncoder(3000, spec, ArrayList())

        println(encoder.constraint!!.toText())
        val concreteSpecification = solver.concretizeSmtModel(encoder.constraint, spec.columnHeaders)
        Assertions.assertNotNull(concreteSpecification)
    }

    @Test
    fun testImported() {
        val spec = importSpec("testSpec.xml")

        val maxDurations = listOf(7, 1, 2)
        val preprocessor = SmtEncoder(maxDurations, spec, freeVariables)
        val concretized = solver.concretizeSmtModel(preprocessor.constraint, spec.columnHeaders)
        Assertions.assertNotNull(concretized)
        val durations = concretized.durations
        Assertions.assertTrue(durations[0].duration in 5..7)
        Assertions.assertEquals(1, durations[1].duration.toLong())
        Assertions.assertEquals(2, durations[2].duration.toLong())
    }

    @Test
    fun process() {
        Assertions.assertNull(solver.process)
        val spec = importSpec("testSpec.xml")
        val preprocessor = SmtEncoder(5, spec, freeVariables)
        solver.concretizeSmtModel(preprocessor.constraint, spec.columnHeaders)

        Assertions.assertNotNull(solver.process)
    }

    @Test
    @Throws(Exception::class)
    fun setZ3Path() {
        solver.z3Path = "testValue"
        Assertions.assertEquals("testValue", solver.z3Path)
        solver.z3Path = "otherValue"
        Assertions.assertEquals("otherValue", solver.z3Path)
    }

    @Test
    @Disabled
    @Throws(Exception::class)
    fun testTerminate() {
        val thread = Thread {
            try {
                val spec = importSpec("spec_long_single_variable_example.xml")
                val preprocessor = SmtEncoder(5, spec, freeVariables)
                solver.concretizeSmtModel(preprocessor.constraint, spec.columnHeaders)
                println("finished")
            } catch (e: Exception) {
                e.printStackTrace()
                Assertions.assertTrue(e is ConcretizationException)
            }
        }
        thread.start()
        println("started")
        Thread.sleep(400)
        println("waiting for process")
        while (solver.process == null) {
        }
        println("interrupt")
        thread.interrupt()
        thread.join()
    }

    @Test
    @Throws(Exception::class)
    fun concretizeSmtModel() {
    }
}