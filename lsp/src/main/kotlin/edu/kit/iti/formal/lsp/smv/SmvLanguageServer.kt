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

import edu.kit.iti.formal.lsp.*
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.parser.SMVParser
import org.antlr.v4.runtime.CharStream
import org.eclipse.lsp4j.*
import org.eclipse.lsp4j.jsonrpc.messages.Either
import org.eclipse.lsp4j.services.LanguageClient
import org.eclipse.lsp4j.services.TextDocumentService
import org.eclipse.lsp4j.services.WorkspaceService
import java.util.*
import java.util.concurrent.CompletableFuture
import java.util.concurrent.CompletableFuture.supplyAsync
import kotlin.io.path.readText

class SmvLanguageServer : MyLanguageServer() {
    private lateinit var initParams: InitializeParams
    override lateinit var client: LanguageClient

    private val wsService: WorkspaceService by lazy {
        SmvTextWorkspaceService(this)
    }

    private val txtService: TextDocumentService by lazy {
        SmvTextTextDocumentService(this)
    }

    val documentHighlighter = SmvDocumentHighlighter()

    override fun getTextDocumentService(): TextDocumentService = txtService
    override fun getWorkspaceService(): WorkspaceService = wsService

    /**
     * Loads LSP actions via ServiceLoader pattern.
     *
     * Extensions can register custom actions by implementing [LspAction] interface
     * and adding a META-INF/services/org.key_project.key.lsp.actions.LspAction file
     * with the fully qualified class name.
     */
    internal val actions by lazy {
        ServiceLoader.load(LspAction::class.java).filterNotNull().toList()
    }

    override fun initialize(params: InitializeParams): CompletableFuture<InitializeResult> {
        this.initParams = params
        val smvFiles = DocumentFilter("smv", "file", Either.forLeft("**/*.key"))

        val capabilities = ServerCapabilities()
        capabilities.setHoverProvider(true)
        capabilities.signatureHelpProvider = SignatureHelpOptions(listOf("<", "("), listOf("<", "(", ","))
        capabilities.foldingRangeProvider = Either.forRight(FoldingRangeProviderOptions("KeY"))
        capabilities.diagnosticProvider = DiagnosticRegistrationOptions(false, true).also {
            it.identifier = "smv-lsp"
            it.documentSelector = listOf(smvFiles)
        }

        capabilities.setDocumentSymbolProvider(true)
        capabilities.setDeclarationProvider(DeclarationRegistrationOptions("KeY"))

        capabilities.setCodeActionProvider(CodeActionOptions(listOf("key")))
        capabilities.executeCommandProvider = ExecuteCommandOptions(actions.map { it.id })
        capabilities.codeLensProvider = CodeLensOptions(true)
        capabilities.selectionRangeProvider = Either.forRight(SelectionRangeRegistrationOptions("KeY"))

        capabilities.setTextDocumentSync(TextDocumentSyncKind.Full)
        capabilities.completionProvider = CompletionOptions(true, listOf(",", "(", ")", "<", ">", "\\"))

        capabilities.semanticTokensProvider = SemanticTokensWithRegistrationOptions(
            documentHighlighter.legend, SemanticTokensServerFull(true), false,
            listOf(smvFiles)
        )
        capabilities.semanticTokensProvider.id = "smv-lsp"
        capabilities.semanticTokensProvider.range = Either.forLeft(true)

        capabilities.documentOnTypeFormattingProvider = null

        capabilities.setDocumentFormattingProvider(true)
        capabilities.setDocumentRangeFormattingProvider(true)
        capabilities.documentLinkProvider = DocumentLinkOptions(false)

        // capabilities.setWorkspaceSymbolProvider(true)

        capabilities.textDocument = TextDocumentServerCapabilities()
        capabilities.textDocument.diagnostic = DiagnosticServerCapabilities().also { it.markupMessageSupport = true }

        // capabilities.workspace = WorkspaceServerCapabilities()
        // capabilities.workspace.workspaceFolders = WorkspaceFoldersOptions().also {
        //    it.supported = true
        //    it.changeNotifications = Either.forRight(true)
        // }

        // capabilities.workspace.textDocumentContent = TextDocumentContentRegistrationOptions(
        //    listOf("jar:file")
        // )

        return CompletableFuture.completedFuture(
            InitializeResult(
                capabilities,
                ServerInfo(
                    "smv-lsp",
                    "0.0.1"
                )
            )
        )
    }
}

class SmvTextTextDocumentService(override val server: SmvLanguageServer) : FileAntlrManager<SMVParser.ModulesContext>(server) {
    override fun parse(x: CharStream): SMVParser.ModulesContext = SMVFacade.getParser(x).modules()

    //region Semantic Tokens
    override fun semanticTokensFull(params: SemanticTokensParams): CompletableFuture<SemanticTokens> =
        supplyAsync { params.textDocument.uri.toPath().readText() }
            .thenApplyAsync { server.documentHighlighter.analyzeText(it) }

    override fun semanticTokensRange(params: SemanticTokensRangeParams): CompletableFuture<SemanticTokens> =
        supplyAsync { (params.textDocument.uri).toPath().readText().substring(params.range.start, params.range.end) }
            .thenApplyAsync { server.documentHighlighter.analyzeText(it) }
    //endregion

    override fun foldingRange(params: FoldingRangeRequestParams): CompletableFuture<List<FoldingRange>> =
        with(SmvFoldingRange) {
            get(params.textDocument.uri).foldingRange()
        }
}

object SmvFoldingRange : FoldingRangeHelper() {
    init {
        register<SMVParser.ModuleContext> { it.name.text }
        register<SMVParser.IVariableDeclarationContext> { "IVAR" }
        register<SMVParser.FrozenVariableDeclarationContext> { "FROZENVAR" }
        register<SMVParser.VariableDeclarationContext> { "VAR" }
        register<SMVParser.NextBodyContext> { null }
        register<SMVParser.TransContext> { "TRANS" }
        register<SMVParser.CtlSpecificationContext> { "CTLSPEC" }
        register<SMVParser.LtlSpecificationContext> { "LTLSPEC" }
        register<SMVParser.PslSpecificationContext> { "PSLSPEC" }
        register<SMVParser.InvarSpecificationContext> { "INVARSPEC" }
        register<SMVParser.InitBodyContext> { null }
        register<SMVParser.VarBodyContext> { null }
        register<SMVParser.AssignConstraintContext> { "ASSIGN" }
    }
}