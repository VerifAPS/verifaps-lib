package edu.kit.iti.formal.automation

import com.google.common.truth.Truth
import edu.kit.iti.formal.automation.st.ast.Pragma
import org.antlr.v4.runtime.CharStreams
import org.junit.jupiter.api.Test

class PragmaTest {
    fun parsePragmaFbd(input: String): List<Pragma> {
        val pous = IEC61131Facade.file(CharStreams.fromString(input))
        return pous.first().pragmas
    }

    @Test
    fun functionBlock1(): Unit {
        val input = """
            {attribute 'warning'}
            function_block abc 
            end_function_block
            """
        val abc = parsePragmaFbd(input).first()
        Truth.assertThat(abc.kind).isEqualTo("attribute")
        (abc as  Pragma.Attribute).let {
            Truth.assertThat(it.name).isEqualTo("warning")
            Truth.assertThat(it.parameters).containsExactly("#0", "warning")
        }
    }

    @Test
    fun functionBlock2(): Unit {
        val input = """
        {attribute 'warning', "abc":="1", "def":="2"}
        function_block def
        end_function_block
        """
        val pragma = parsePragmaFbd(input).first()
        Truth.assertThat(pragma.kind).isEqualTo("attribute")
        (pragma as  Pragma.Attribute).let {
            Truth.assertThat(it.name).isEqualTo("warning")
            Truth.assertThat(it.parameters).containsExactly("abc", "1", "def", "2", "#0", "warning")
        }
    }


    @Test
    fun functionBlock3(): Unit {
        val input = """
        {attribute 'first'}
        {attribute 'second'}
        function_block ghi
        end_function_block
        """.trimIndent()
        val pragmas = parsePragmaFbd(input)
        val f = pragmas[0]
        val s = pragmas[1]
        (f as Pragma.Attribute).let {
            Truth.assertThat(it.name).isEqualTo("first")
        }
        (s as  Pragma.Attribute).let {
            Truth.assertThat(it.name).isEqualTo("second")
        }
    }
}