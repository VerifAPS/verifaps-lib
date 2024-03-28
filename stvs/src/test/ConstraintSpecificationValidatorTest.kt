package edu.kit.iti.formal.stvs.model.table

import edu.kit.iti.formal.stvs.model.expressions.Type
import javafx.beans.property.SimpleObjectProperty
import org.junit.Assert
import org.junit.jupiter.api.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.util.*
import java.util.function.Consumer
import java.util.function.Predicate

/**
 * @author Benjamin Alt
 * @author Philipp
 */
@RunWith(Parameterized::class)
class ConstraintSpecificationValidatorTest {
    @Parameterized.Parameter
    var testfile: String? = null

    @Test
    fun testProblems() {
        val testjson: JsonElement? =
            JsonTableParser.jsonFromResource(testfile, ConstraintSpecificationValidatorTest::class.java)

        val codeIoVariables: List<CodeIoVariable?>? = JsonTableParser.codeIoVariablesFromJson(testjson)

        val typeContext = Arrays.asList<Type>(TypeInt.INT, TypeBool.BOOL)

        val freeVars: FreeVariableList? = JsonTableParser.freeVariableSetFromJson(testjson)

        val testSpec =
            JsonTableParser.constraintTableFromJson(testjson)

        val validator: FreeVariableListValidator = FreeVariableListValidator(
            SimpleObjectProperty<List<Type>>(typeContext),
            freeVars
        )

        val recognizer: ConstraintSpecificationValidator = ConstraintSpecificationValidator(
            SimpleObjectProperty<List<Type>>(typeContext),
            SimpleObjectProperty<List<CodeIoVariable?>?>(codeIoVariables),
            validator.validFreeVariablesProperty(),
            testSpec
        )

        val expectedProblems = JsonTableParser.expectedSpecProblemsFromJson(testjson)

        println("Expecting problems: " + expectedProblems!!.stream().map<String> { obj: Class<*>? -> obj!!.simpleName }
            .collect(Collectors.toList<String>()))

        println("Actual Problems: ")
        recognizer.problemsProperty().get().forEach(Consumer<SpecProblem> { x: SpecProblem? -> println(x) })

        Assert.assertEquals(
            "Problem list emptiness: ",
            expectedProblems.isEmpty(),
            recognizer.problemsProperty().get().isEmpty()
        )
        Assert.assertTrue(
            expectedProblems.stream().allMatch { aClass: Class<*>? ->
                recognizer.problemsProperty().get().stream().anyMatch(
                    Predicate<SpecProblem> { obj: SpecProblem? -> aClass!!.isInstance(obj) })
            })
    }

    companion object {
        @Parameterized.Parameters(name = "{0}")
        fun testfiles(): Collection<String> {
            return mutableListOf(
                "valid_table.json",
                "invalid_cell_type.json",
                "unknown_cell_variable.json",
                "unknown_iovar.json",
                "invalid_iovar_type.json",
                "invalid_cell_grammar.json",
                "unsupported_cell_grammar.json",
                "invalid_duration_grammar.json"
            )
        }
    }
}