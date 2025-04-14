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
            FXCollections.observableArrayList(TypeInt, TypeBool)
        )
        val validator = FreeVariableListValidator(typeContext, FreeVariableList(variables.toMutableList()))
        checkProblems(expectedProblem, variables, validator)
    }

    private fun checkProblems(
        expectedProblem: String,
        variables: List<FreeVariable>,
        validator: FreeVariableListValidator
    ) {
        if (expectedProblem.isEmpty()) {
            validator.problemsProperty.get().values.forEach(System.out::println)
            Assertions.assertEquals(
                variables.size,
                validator.validFreeVariablesProperty.get().size,
                "Number of valid free variables should be equal to number of unvalidated"
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
            "Problems contain only expected problems"
        )
    }

    companion object {
        @JvmStatic
        fun parameters(): List<Arguments> {
            return listOf(
                Arguments.of("", listOf(FreeVariable("a", "INT"), FreeVariable("b", "BOOL"))),
                Arguments.of(
                    "InvalidFreeVariableProblem",
                    listOf(FreeVariable("a xy _%", "INT"), FreeVariable("b", "BOOL"))
                ),
                Arguments.of(
                    "InvalidFreeVariableProblem",
                    listOf(FreeVariable("a", "INT"), FreeVariable("b", "BOOLEAN"))
                ),
                Arguments.of(
                    "InvalidFreeVariableProblem",
                    listOf(FreeVariable("a", "INT", "asf"), FreeVariable("b", "BOOL"))
                ),
                Arguments.of(
                    "InvalidFreeVariableProblem",
                    listOf(FreeVariable("a", "INT", "TRUE"), FreeVariable("b", "BOOL"))
                ),
                Arguments.of("", listOf(FreeVariable("a", "INT", "1"), FreeVariable("b", "BOOL", "TRUE"))),
                Arguments.of(
                    "DuplicateFreeVariableProblem",
                    listOf(FreeVariable("my_variable", "INT"), FreeVariable("my_variable", "BOOL"))
                )
            )
        }
    }
}