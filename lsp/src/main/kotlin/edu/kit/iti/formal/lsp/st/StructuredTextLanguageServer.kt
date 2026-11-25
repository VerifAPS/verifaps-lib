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

import edu.kit.iti.formal.automation.*
import edu.kit.iti.formal.automation.parser.*
import edu.kit.iti.formal.lsp.*
import org.antlr.v4.runtime.CharStream
import org.eclipse.lsp4j.*
import org.eclipse.lsp4j.jsonrpc.messages.Either
import org.eclipse.lsp4j.services.LanguageClient
import org.eclipse.lsp4j.services.TextDocumentService
import org.eclipse.lsp4j.services.WorkspaceService
import java.util.concurrent.CompletableFuture
import java.util.concurrent.CompletableFuture.supplyAsync
import kotlin.io.path.readText

class StructuredTextLanguageServer : MyLanguageServer() {
    val documentHighlighter = StDocumentHighlighter()

    override lateinit var client: LanguageClient

    private val wsService: WorkspaceService by lazy {
        StructuredTextWorkspaceService(this)
    }

    private val txtService: TextDocumentService by lazy {
        StructuredTextTextDocumentService(this)
    }

    override fun initialize(params: InitializeParams): CompletableFuture<InitializeResult> {
        val capabilities = ServerCapabilities()
        capabilities.setTextDocumentSync(TextDocumentSyncKind.Full)

        capabilities.semanticTokensProvider = SemanticTokensWithRegistrationOptions(
            documentHighlighter.legend, SemanticTokensServerFull(true), false,
            listOf(DocumentFilter("st", "file", Either.forLeft("**/*.st")))
        )
        capabilities.semanticTokensProvider.range = Either.forLeft(true)
        capabilities.foldingRangeProvider = Either.forLeft(true)

        return CompletableFuture.completedFuture(
            InitializeResult(capabilities, ServerInfo("verifaps-st", "0.0.1")),
        )
    }

    override fun getTextDocumentService(): TextDocumentService = txtService
    override fun getWorkspaceService(): WorkspaceService = wsService
}

class StructuredTextTextDocumentService(override val server: StructuredTextLanguageServer) : FileAntlrManager<IEC61131Parser.StartContext>(server) {
    override fun parse(x: CharStream): IEC61131Parser.StartContext {
        val p = IEC61131Facade.getParser(x)
        val ctx = p.start()
        p.errorReporter.throwException()
        return ctx
    }

    //region Semantic Tokens
    override fun semanticTokensFull(params: SemanticTokensParams): CompletableFuture<SemanticTokens> =
        supplyAsync { params.textDocument.uri.toPath().readText() }
            .thenApplyAsync { server.documentHighlighter.analyzeText(it) }

    override fun semanticTokensRange(params: SemanticTokensRangeParams): CompletableFuture<SemanticTokens> =
        supplyAsync { (params.textDocument.uri).toPath().readText().substring(params.range.start, params.range.end) }
            .thenApplyAsync { server.documentHighlighter.analyzeText(it) }
    //endregion

    override fun foldingRange(params: FoldingRangeRequestParams): CompletableFuture<List<FoldingRange>> =
        with(StructuredTextFoldingRange) {
            get(params.textDocument.uri).foldingRange()
        }
}

class StructuredTextWorkspaceService(val server: StructuredTextLanguageServer) : WorkspaceService {
    override fun didChangeConfiguration(params: DidChangeConfigurationParams) {
        // No configuration is currently supported.
    }

    override fun didChangeWatchedFiles(params: DidChangeWatchedFilesParams) {
        // Documents are re-read on open, change, and save.
    }
}