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
package edu.kit.iti.formal.lsp

import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.lsp.st.StDocumentHighlighter
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.Lexer
import org.antlr.v4.runtime.Token
import org.eclipse.lsp4j.Position
import org.eclipse.lsp4j.Range
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import java.nio.file.Path

class HighlighterTest {
    private class StTestHighlighter : Highlighter() {
        private val delegate = StDocumentHighlighter()

        override fun createLexer(it: String): Lexer = IEC61131Lexer(CharStreams.fromString(it))

        override fun createLexer(it: Path): Lexer = IEC61131Lexer(CharStreams.fromPath(it))

        override fun tokenModifier(token: Token): Int = delegate.tokenModifier(token)

        override fun tokenType(token: Token): Int? = delegate.tokenType(token)
    }

    @Test
    fun `a multi line block comment is split into one token per line`() {
        val tokens = StTestHighlighter().analyzeText("/* a\nb */")

        assertEquals(10, tokens.data.size)
        assertEquals(0, tokens.data[0].toInt())
        assertEquals(0, tokens.data[1].toInt())
        assertEquals(4, tokens.data[2].toInt())
        assertEquals(1, tokens.data[5].toInt())
        assertEquals(0, tokens.data[6].toInt())
        assertEquals(4, tokens.data[7].toInt())
    }

    @Test
    fun `range tokens keep absolute line numbers`() {
        val text = """
            PROGRAM P
            VAR
                x : INT;
            END_VAR
            x := 1;
            END_PROGRAM
        """.trimIndent()

        val tokens = StTestHighlighter().analyzeText(text, Range(Position(4, 0), Position(5, 0)))

        assertTrue(tokens.data.isNotEmpty())
        assertEquals(4, tokens.data[0].toInt())
    }
}