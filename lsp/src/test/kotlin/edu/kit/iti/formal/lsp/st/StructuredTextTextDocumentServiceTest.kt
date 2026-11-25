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
package edu.kit.iti.formal.lsp.st

import org.eclipse.lsp4j.FoldingRangeRequestParams
import org.eclipse.lsp4j.Position
import org.eclipse.lsp4j.Range
import org.eclipse.lsp4j.SemanticTokensParams
import org.eclipse.lsp4j.SemanticTokensRangeParams
import org.eclipse.lsp4j.TextDocumentIdentifier
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import java.nio.file.Files

class StructuredTextTextDocumentServiceTest {
    private fun service() =
        StructuredTextLanguageServer().getTextDocumentService() as StructuredTextTextDocumentService

    private fun file(content: String) =
        Files.createTempFile("lsp", ".st").also { Files.writeString(it, content) }

    @Test
    fun `empty file yields no tokens or folding ranges`() {
        val uri = file("").toUri().toString()
        val service = service()

        assertTrue(service.semanticTokensFull(SemanticTokensParams(TextDocumentIdentifier(uri))).get().data.isEmpty())
        assertTrue(service.foldingRange(FoldingRangeRequestParams(TextDocumentIdentifier(uri))).get().isEmpty())
    }

    @Test
    fun `a program without a trailing newline still yields tokens`() {
        val uri = file("PROGRAM P\nVAR\n x : INT;\nEND_VAR\nx := 1;\nEND_PROGRAM").toUri().toString()
        val service = service()

        assertTrue(service.semanticTokensFull(SemanticTokensParams(TextDocumentIdentifier(uri))).get().data.isNotEmpty())
    }

    @Test
    fun `range tokens start at the requested absolute line`() {
        val uri = file("PROGRAM P\nVAR\n x : INT;\nEND_VAR\nx := 1;\nEND_PROGRAM\n").toUri().toString()
        val service = service()

        val tokens = service.semanticTokensRange(
            SemanticTokensRangeParams(
                TextDocumentIdentifier(uri),
                Range(Position(4, 0), Position(5, 0)),
            ),
        ).get()

        assertTrue(tokens.data.isNotEmpty())
        assertEquals(4, tokens.data[0].toInt())
    }
}