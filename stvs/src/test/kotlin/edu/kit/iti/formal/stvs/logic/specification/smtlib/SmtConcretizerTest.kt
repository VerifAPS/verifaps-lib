package edu.kit.iti.formal.stvs.logic.specification.smtlib

import edu.kit.iti.formal.stvs.*
import edu.kit.iti.formal.stvs.logic.io.ImportException
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
import javafx.beans.property.*
import org.junit.jupiter.api.BeforeEach
import org.junit.Rule
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import org.junit.rules.Stopwatch
import tornadofx.asObservable
import java.util.*
import java.util.concurrent.TimeUnit

/**
 * Created by csicar on 13.02.17.
 */
class SmtConcretizerTest {
    private var freeVariables: List<ValidFreeVariable>? = null

    private fun importSpec(name: String): ValidSpecification? {
        val typeContext = listOf(
            TypeInt.INT, TypeBool.BOOL, TypeEnum(
                "colors",
                mutableListOf("red", "green", "blue")
            )
        )
        val codeIoVariables: List<CodeIoVariable> = LinkedList()

        val constraintSpec: ConstraintSpecification =
            ImporterFacade.importConstraintSpec(javaClass.getResourceAsStream(name)!!)
        val freeVariableListValidator =
            FreeVariableListValidator(SimpleListProperty(typeContext.asObservable()), constraintSpec.freeVariableList)
        val freeVariables: List<ValidFreeVariable> = freeVariableListValidator.validFreeVariablesProperty.get()
        this.freeVariables = freeVariables
        val validator = ConstraintSpecificationValidator(
            SimpleListProperty(typeContext.asObservable()),
            SimpleListProperty(codeIoVariables.asObservable()),
            freeVariables.asObservable(),
            constraintSpec
        )
        val specProblems = validator.problemsProperty().get()
        specProblems.map { it?.errorMessage }.forEach { println(it) }

        return validator.getValidSpecification()
    }

    @JvmField
    @Rule
    var stopwatch: Stopwatch = Stopwatch()

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
        val start = stopwatch.runtime(TimeUnit.MILLISECONDS)
        concretizer.terminate()
        val end = stopwatch.runtime(TimeUnit.MILLISECONDS)
        val maxTime: Long = 5
        Assertions.assertTrue(
            end - start < maxTime,
            "Except time to terminate to be smaller than " + maxTime + ", but was" + (end - start)
        )
    }

    @Test
    fun simpleTest() {
        val spec = importSpec("testSpec.xml")
        val maxDurations: Map<Int, Int> = mapOf(0 to 7, 1 to 1, 2 to 2)
        val concretizer = SmtConcretizer(autoloadConfig())
        concretizer.calculateConcreteSpecification(spec, freeVariables!!)
    }
}