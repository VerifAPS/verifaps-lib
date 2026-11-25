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

import org.eclipse.lsp4j.InitializeParams
import org.eclipse.lsp4j.TextDocumentSyncKind
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertNull
import org.junit.jupiter.api.Test

class SmvLanguageServerTest {
    @Test
    fun `initialize advertises smv sync, tokens, folding only`() {
        val caps = SmvLanguageServer().initialize(InitializeParams()).get().capabilities

        assertEquals(TextDocumentSyncKind.Full, caps.textDocumentSync.left)
        assertEquals("**/*.smv", caps.semanticTokensProvider.documentSelector.single().pattern.left)
        assertEquals(true, caps.foldingRangeProvider.left)
        assertNull(caps.hoverProvider)
        assertNull(caps.codeActionProvider)
        assertNull(caps.executeCommandProvider)
    }
}