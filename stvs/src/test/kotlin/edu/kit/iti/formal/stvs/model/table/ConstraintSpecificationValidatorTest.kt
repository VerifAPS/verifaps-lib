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
        invalid_duration_grammar.json"""
    )
    fun testProblems(testfile: String) {
        val testJson = JsonTableParser.jsonFromResource(testfile, ConstraintSpecificationValidatorTest::class.java)
        val codeIoVariables = JsonTableParser.codeIoVariablesFromJson(testJson).asObservable()
        val typeContext = listOf(TypeInt, TypeBool).asObservable()
        val freeVars = JsonTableParser.freeVariableSetFromJson(testJson)

        val testSpec = JsonTableParser.constraintTableFromJson(testJson)
        val validator = FreeVariableListValidator(
            SimpleListProperty(typeContext),
            freeVars
        )

        val recognizer = ConstraintSpecificationValidator(
            SimpleListProperty(typeContext),
            SimpleListProperty(codeIoVariables),
            validator.validFreeVariablesProperty,
            testSpec
        )

        val expectedProblems = JsonTableParser.expectedSpecProblemsFromJson(testJson)

        val exp = expectedProblems.map { it.simpleName }.toSortedSet()
        val act = recognizer.problems.map { it.javaClass.simpleName }.toSortedSet()

        Truth.assertThat(act).isEqualTo(exp)
    }
}