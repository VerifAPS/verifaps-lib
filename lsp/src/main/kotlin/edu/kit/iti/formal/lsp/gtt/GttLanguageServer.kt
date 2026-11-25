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

import edu.kit.iti.formal.lsp.MyLanguageServer
import org.eclipse.lsp4j.DocumentFilter
import org.eclipse.lsp4j.InitializeParams
import org.eclipse.lsp4j.InitializeResult
import org.eclipse.lsp4j.SemanticTokensServerFull
import org.eclipse.lsp4j.SemanticTokensWithRegistrationOptions
import org.eclipse.lsp4j.ServerCapabilities
import org.eclipse.lsp4j.ServerInfo
import org.eclipse.lsp4j.TextDocumentSyncKind
import org.eclipse.lsp4j.jsonrpc.messages.Either
import org.eclipse.lsp4j.services.LanguageClient
import org.eclipse.lsp4j.services.WorkspaceService
import java.util.concurrent.CompletableFuture

/**
 * Language Server for Generalized Test Tables (GTT).
 */
class GttLanguageServer : MyLanguageServer() {
    override lateinit var client: LanguageClient

    val documentHighlighter = GttDocumentHighlighter()

    private val wsService: WorkspaceService by lazy {
        GttTextWorkspaceService(this)
    }

    private val txtService: GttTextDocumentService by lazy {
        GttTextDocumentService(this)
    }

    override fun initialize(params: InitializeParams): CompletableFuture<InitializeResult> {
        val capabilities = ServerCapabilities()
        capabilities.setTextDocumentSync(TextDocumentSyncKind.Full)

        capabilities.semanticTokensProvider = SemanticTokensWithRegistrationOptions(
            documentHighlighter.legend, SemanticTokensServerFull(false), false,
            listOf(DocumentFilter("gtt", "file", Either.forLeft("**/*.gtt")))
        )
        capabilities.semanticTokensProvider.range = Either.forLeft(true)
        capabilities.foldingRangeProvider = Either.forLeft(true)

        return CompletableFuture.completedFuture(
            InitializeResult(capabilities, ServerInfo("verifaps-gtt", "0.0.1")),
        )
    }

    override fun getTextDocumentService(): GttTextDocumentService = txtService

    override fun getWorkspaceService(): WorkspaceService = wsService
}