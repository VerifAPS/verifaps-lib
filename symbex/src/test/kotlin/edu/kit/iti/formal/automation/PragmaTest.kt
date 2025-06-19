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
    fun functionBlock1() {
        val input = """
            {attribute 'warning'}
            function_block abc 
            end_function_block
            """
        val abc = parsePragmaFbd(input).first()
        Truth.assertThat(abc.kind).isEqualTo("attribute")
        (abc as Pragma.Attribute).let {
            Truth.assertThat(it.name).isEqualTo("warning")
            Truth.assertThat(it.parameters).containsExactly("#0", "warning")
        }
    }

    @Test
    fun functionBlock2() {
        val input = """
        {attribute 'warning', "abc":="1", "def":="2"}
        function_block def
        end_function_block
        """
        val pragma = parsePragmaFbd(input).first()
        Truth.assertThat(pragma.kind).isEqualTo("attribute")
        (pragma as Pragma.Attribute).let {
            Truth.assertThat(it.name).isEqualTo("warning")
            Truth.assertThat(it.parameters).containsExactly("abc", "1", "def", "2", "#0", "warning")
        }
    }

    @Test
    fun functionBlock3() {
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
        (s as Pragma.Attribute).let {
            Truth.assertThat(it.name).isEqualTo("second")
        }
    }
}
