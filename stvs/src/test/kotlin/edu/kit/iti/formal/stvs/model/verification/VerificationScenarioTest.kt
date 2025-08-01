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
package edu.kit.iti.formal.stvs.model.verification

import edu.kit.iti.formal.stvs.StvsApplication
import edu.kit.iti.formal.stvs.TestUtils
import edu.kit.iti.formal.stvs.TestUtils.loadFromTestSets
import edu.kit.iti.formal.stvs.logic.io.ImportException
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade.importStCode
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade.importVerificationResult
import edu.kit.iti.formal.stvs.model.code.Code
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.model.config.GlobalConfig.Companion.autoloadConfig
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeFactory.enumOfName
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification
import javafx.beans.value.ChangeListener
import javafx.beans.value.ObservableValue
import junit.framework.AssertionFailedError
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Test
import java.io.File
import java.io.IOException
import java.net.URISyntaxException
import kotlin.time.measureTimedValue

/**
 * Created by bal on 26.02.17.
 */
class VerificationScenarioTest {
    private lateinit var scenario: VerificationScenario
    private lateinit var constraintSpec: ConstraintSpecification
    private lateinit var config: GlobalConfig
    private lateinit var code: Code

    @Volatile
    private var done = false

    @BeforeEach
    @Throws(URISyntaxException::class, IOException::class, ImportException::class)
    fun setUp() {
        TestUtils.assumeNuXmvExists()
        scenario = VerificationScenario()
        code = importStCode(File(StvsApplication::class.java.getResource("testSets/valid_1/code_valid_1.st")!!.toURI()))
        constraintSpec = ImporterFacade.importConstraintSpec(
            loadFromTestSets("/valid_1/constraint_spec_valid_1.xml"),
        )
        scenario.code = code
        config = autoloadConfig()
    }

    @Test
    @Throws(Exception::class)
    @Disabled
    fun testVerify() {
        scenario.verificationResultProperty.addListener(VerificationResultListener())
        Assertions.assertEquals(VerificationState.NOT_STARTED, scenario.verificationState)
        scenario.verify(config, constraintSpec)
        Assertions.assertEquals(VerificationState.RUNNING, scenario.verificationState)
        done = false
        val startTime = measureTimedValue {
            while (!done) {
                Thread.sleep(500)
            }
        }
    }

    @Test
    @Throws(Exception::class)
    @Disabled
    fun testCancel() {
        Assertions.assertEquals(VerificationState.NOT_STARTED, scenario.verificationState)
        scenario.verify(config, constraintSpec)
        Assertions.assertEquals(VerificationState.RUNNING, scenario.verificationState)
        scenario.cancel()
        Assertions.assertEquals(VerificationState.CANCELLED, scenario.verificationState)
    }

    @Test
    @Throws(Exception::class)
    fun testGetCode() {
        Assertions.assertEquals(code, scenario.code)
    }

    @Test
    @Throws(Exception::class)
    fun testSetCode() {
        val emptyScenario = VerificationScenario()
        Assertions.assertEquals(Code(), emptyScenario.code)
        emptyScenario.code = code
        Assertions.assertEquals(code, emptyScenario.code)
    }

    @Test
    @Throws(Exception::class)
    fun testGetSetActiveSpec() {
        Assertions.assertNull(scenario.activeSpec)
        scenario.activeSpec = constraintSpec
        Assertions.assertEquals(constraintSpec, scenario.activeSpec)
    }

    private inner class VerificationResultListener : ChangeListener<VerificationResult> {
        override fun changed(
            observableValue: ObservableValue<out VerificationResult>,
            old: VerificationResult,
            newResult: VerificationResult,
        ) {
            val typeContext = listOf(TypeInt, TypeBool, enumOfName("enumD", "literalOne", "literalTwo"))
            try {
                val constraintSpec: ConstraintSpecification = ImporterFacade.importConstraintSpec(
                    loadFromTestSets("/valid_1/constraint_spec_valid_1.xml"),
                )
                val expectedResult = importVerificationResult(
                    loadFromTestSets("/valid_1/geteta_report_valid_1.xml"),
                    typeContext,
                    constraintSpec,
                )
                /* Cannot just assertEquals() with verificationResults, as logFileNames
                (randomly generated) will be different assertEquals(expectedResult, newResult); */
                Assertions.assertEquals(expectedResult.javaClass, newResult.javaClass)
            } catch (_: ImportException) {
                throw AssertionFailedError()
            }
            done = true
        }
    }

    companion object {
        private const val TIMEOUT: Long = 5000
    }
}