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
package edu.kit.iti.formal.lsp.smv

import edu.kit.iti.formal.automation.parser.SyntaxErrorReporter
import org.eclipse.lsp4j.FoldingRangeRequestParams
import org.eclipse.lsp4j.InitializeParams
import org.eclipse.lsp4j.SemanticTokensParams
import org.eclipse.lsp4j.TextDocumentIdentifier
import org.eclipse.lsp4j.TextDocumentSyncKind
import org.junit.jupiter.api.Assertions.assertDoesNotThrow
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Assertions.assertThrows
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import java.nio.file.Files

class SmvLanguageServerTest {
    @Test
    fun `initialize advertises smv sync, tokens, folding only`() {
        val caps = SmvLanguageServer().initialize(InitializeParams()).get().capabilities

        assertEquals(TextDocumentSyncKind.Full, caps.textDocumentSync.left)
        assertEquals(false, caps.semanticTokensProvider.full.right.delta)
        assertEquals("**/*.smv", caps.semanticTokensProvider.documentSelector.single().pattern.left)
        assertEquals(true, caps.foldingRangeProvider.left)
        assertNull(caps.hoverProvider)
        assertNull(caps.codeActionProvider)
        assertNull(caps.executeCommandProvider)
    }

    @Test
    fun `a broken smv file is reported as a parse error`() {
        val file = Files.createTempFile("lsp", ".smv")
        Files.writeString(file, "MODULE main VAR x : ;")
        val service = SmvLanguageServer().getTextDocumentService() as SmvTextTextDocumentService

        assertThrows(SyntaxErrorReporter.ParserException::class.java) {
            service.getSync(file.toUri().toString())
        }
    }

    @Test
    fun `a valid smv file yields tokens and folding ranges`() {
        val file = Files.createTempFile("lsp", ".smv")
        Files.writeString(file, "MODULE main\nVAR\n  x : boolean;\nASSIGN\n  init(x) := FALSE;\n")
        val uri = file.toUri().toString()
        val service = SmvLanguageServer().getTextDocumentService() as SmvTextTextDocumentService

        assertDoesNotThrow { service.getSync(uri) }
        assertTrue(service.semanticTokensFull(SemanticTokensParams(TextDocumentIdentifier(uri))).get().data.isNotEmpty())
        assertTrue(service.foldingRange(FoldingRangeRequestParams(TextDocumentIdentifier(uri))).get().isNotEmpty())
    }
}