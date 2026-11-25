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
package edu.kit.iti.formal.lsp.gtt

import org.eclipse.lsp4j.FoldingRangeRequestParams
import org.eclipse.lsp4j.InitializeParams
import org.eclipse.lsp4j.SemanticTokensParams
import org.eclipse.lsp4j.TextDocumentIdentifier
import org.eclipse.lsp4j.TextDocumentSyncKind
import org.junit.jupiter.api.Assertions.assertDoesNotThrow
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import java.nio.file.Files

class GttLanguageServerTest {
    private val sample = """
        table Ta {
            var input i_fWeight : INT
            group 0 [1, 1] {
                row initWait [5,5] {
                    i_fWeight: 0
                }
            }
        }
    """.trimIndent()

    @Test
    fun `initialize advertises gtt capabilities`() {
        val caps = GttLanguageServer().initialize(InitializeParams()).get().capabilities

        assertEquals(TextDocumentSyncKind.Full, caps.textDocumentSync.left)
        assertEquals(false, caps.semanticTokensProvider.full.right.delta)
        assertEquals("**/*.gtt", caps.semanticTokensProvider.documentSelector.single().pattern.left)
        assertNotNull(caps.foldingRangeProvider)
    }

    @Test
    fun `text document service parses a gtt and returns tokens`() {
        val file = Files.createTempFile("lsp", ".gtt")
        Files.writeString(file, sample)
        val uri = file.toUri().toString()
        val service = GttLanguageServer().getTextDocumentService()

        assertDoesNotThrow { service.getSync(uri) }

        val tokens = service.semanticTokensFull(SemanticTokensParams(TextDocumentIdentifier(uri))).get()
        assertTrue(tokens.data.isNotEmpty())
    }

    @Test
    fun `gtt table produces a folding range`() {
        val file = Files.createTempFile("lsp", ".gtt")
        Files.writeString(file, sample)
        val service = GttLanguageServer().getTextDocumentService()

        val ranges = service.foldingRange(FoldingRangeRequestParams(TextDocumentIdentifier(file.toUri().toString()))).get()

        assertTrue(ranges.any { it.startLine == 0 })
    }
}