package edu.kit.iti.formal.stvs.model.code

import com.google.common.truth.Truth
import edu.kit.iti.formal.stvs.TestUtils.loadCodeFromFile
import edu.kit.iti.formal.stvs.model.TestUtils
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable
import edu.kit.iti.formal.stvs.model.common.VariableCategory
import edu.kit.iti.formal.stvs.model.expressions.Type
import edu.kit.iti.formal.stvs.model.expressions.TypeBool
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum
import edu.kit.iti.formal.stvs.model.expressions.TypeInt
import org.antlr.v4.runtime.Token
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Disabled
import org.junit.jupiter.api.Test

/**
 * Created by Philipp on 19.01.2017.
 */
class CodeTest {
    private val code = Code()
    private val enumDefinition = loadCodeFromFile("define_type.st")
    private val invalidCode = loadCodeFromFile("invalidCode.st")

    @Test
    fun testIsEmptyInitially() {
        Assertions.assertEquals("", code.sourcecode)
    }

    @Test
    fun testTokensExist() {
        code.updateSourcecode("TYPE is a keyword END_TYPE")
        val tokens: List<Token> = code.tokens
        println(tokens)
        Assertions.assertTrue(tokens.isNotEmpty())
    }

    @Test
    @Disabled
    fun testUnicodeChars() {
        code.updateSourcecode("öüäß")
        val tokens: List<Token> = code.tokens
        println(tokens)
        Assertions.assertTrue(tokens.isNotEmpty())
    }

    @Test
    fun testTokensConcatenated() {
        val source = enumDefinition.sourcecode
        val tokens: List<Token> = enumDefinition.tokens
        val tokensConcatenated = tokens.joinToString("") { it.text }
        Assertions.assertEquals(source, tokensConcatenated, "Lexer tokens concatenated are source code")
    }

    @Test
    fun testParsedCodeTypeExtraction() {
        val parsed = enumDefinition.parsedCode!!
        Assertions.assertEquals(3, parsed.definedTypes.size.toLong(), "Find all defined Types")

        val myEnum: Type = TypeEnum("MY_ENUM", mutableListOf("possible", "values", "enum"))
        val expectedDefinedTypes: MutableSet<Type> = HashSet()
        expectedDefinedTypes.add(TypeBool.BOOL)
        expectedDefinedTypes.add(TypeInt.INT)
        expectedDefinedTypes.add(myEnum)
        TestUtils.assertCollectionsEqual(expectedDefinedTypes, parsed.definedTypes)
    }

    @Test
    fun testParsedCodeIOVariableExtraction() {
        val parsed = enumDefinition.parsedCode!!
        //Assertions.assertEquals(7, parsed.definedVariables.size.toLong(), "Find all defined IOVariables")

        val myEnum: Type = TypeEnum("MY_ENUM", mutableListOf("possible", "values", "enum"))
        val expectedVariables = setOf(
            CodeIoVariable(VariableCategory.INPUT, "BOOL", "active"),
            CodeIoVariable(VariableCategory.INPUT, "INT", "number"),
            CodeIoVariable(VariableCategory.INPUT, myEnum.typeName, "my_enum"),
            CodeIoVariable(VariableCategory.OUTPUT, myEnum.typeName, "my_output"),
            CodeIoVariable(VariableCategory.OUTPUT, "BOOL", "seriously"),
            CodeIoVariable(VariableCategory.LOCAL, myEnum.typeName, "my_enum_local"),
            CodeIoVariable(VariableCategory.INOUT, "BOOL", "active_inout")
        )
        Truth.assertThat(parsed.definedVariables.toSet()).isEqualTo(expectedVariables)
    }

    @Test
    fun testParsedCodeBlocks() {
        val expectedBlock = FoldableCodeBlock(5, 27)
        val pcode = enumDefinition.parsedCode!!
        Assertions.assertEquals(expectedBlock, pcode.foldableCodeBlocks[0])
        Assertions.assertEquals(1, pcode.foldableCodeBlocks.size.toLong())
        Assertions.assertEquals(5, pcode.foldableCodeBlocks[0].startLine.toLong())
        Assertions.assertEquals(27, pcode.foldableCodeBlocks[0].endLine.toLong())
    }

    @Test
    fun testInvalidCode() {
        Assertions.assertNotNull(invalidCode.syntaxErrors.size)
    }

    @Test
    fun testEquals() {
        Assertions.assertEquals(enumDefinition, enumDefinition)
        Assertions.assertEquals(loadCodeFromFile("define_type.st"), enumDefinition)
        Assertions.assertNotEquals(invalidCode, enumDefinition)
        Assertions.assertNotEquals(null, enumDefinition)
    }

    @Test
    fun testHashCode() {
        Assertions.assertEquals(enumDefinition.hashCode().toLong(), enumDefinition.hashCode().toLong())
        Assertions.assertEquals(
            loadCodeFromFile("define_type.st").hashCode().toLong(),
            enumDefinition.hashCode().toLong()
        )
        Assertions.assertNotEquals(invalidCode.hashCode().toLong(), enumDefinition.hashCode().toLong())
    }
}
