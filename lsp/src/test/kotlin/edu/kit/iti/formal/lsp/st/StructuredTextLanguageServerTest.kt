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

import edu.kit.iti.formal.automation.IEC61131Facade
import org.antlr.v4.runtime.CharStreams
import org.eclipse.lsp4j.InitializeParams
import org.eclipse.lsp4j.TextDocumentSyncKind
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNotNull
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import java.util.concurrent.CompletableFuture

class StructuredTextLanguageServerTest {
    private val sample = """
        PROGRAM P
        VAR
            x : INT;
        END_VAR
        x := 1;
        END_PROGRAM
    """.trimIndent()

    @Test
    fun `initialize advertises sync, semantic tokens, and folding for st`() {
        val caps = StructuredTextLanguageServer().initialize(InitializeParams()).get().capabilities

        assertEquals(TextDocumentSyncKind.Full, caps.textDocumentSync.left)
        assertNotNull(caps.semanticTokensProvider)
        assertEquals(true, caps.foldingRangeProvider.left)
        assertEquals("**/*.st", caps.semanticTokensProvider.documentSelector.single().pattern.left)
        assertNull(caps.hoverProvider)
    }

    @Test
    fun `the program declaration produces a folding range starting at line zero`() {
        val context = IEC61131Facade.getParser(CharStreams.fromString(sample)).start()

        val ranges = with(StructuredTextFoldingRange) {
            CompletableFuture.completedFuture(context).foldingRange().get()
        }

        assertTrue(ranges.any { it.startLine == 0 && it.collapsedText == "P" })
    }
}