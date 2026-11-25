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

import edu.kit.iti.formal.automation.parser.SyntaxErrorReporter
import org.antlr.v4.runtime.CommonToken
import org.antlr.v4.runtime.misc.ParseCancellationException
import org.eclipse.lsp4j.Position
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import java.nio.file.Files

class UtilTest {
    @Test
    fun `substring uses the line start, not the newline index`() {
        assertEquals("c", "a\nbc".substring(Position(1, 1), Position(1, 2)))
    }

    @Test
    fun `parser diagnostics are 0-based and cover the token`() {
        val token = CommonToken(0).apply { text = "abc" }
        val error = SyntaxErrorReporter.SyntaxError(
            line = 2,
            charPositionInLine = 3,
            msg = "x",
            offendingSymbol = token,
            stack = "",
        )

        val diagnostic = SyntaxErrorReporter.ParserException("", listOf(error)).toDiagnostics().single()

        assertEquals(Position(1, 3), diagnostic.range.start)
        assertEquals(Position(1, 6), diagnostic.range.end)
        assertEquals("x", diagnostic.message.left)
    }

    @Test
    fun `file uris with spaces decode`() {
        val file = Files.createTempFile("lsp space", ".st")

        assertEquals(file, file.toUri().toString().toPath())
    }

    @Test
    fun `parse cancellation extracts line and column`() {
        val diagnostic = ParseCancellationException("line 3:4 mismatched input").toDiagnostics().single()

        assertEquals(Position(2, 4), diagnostic.range.start)
    }
}