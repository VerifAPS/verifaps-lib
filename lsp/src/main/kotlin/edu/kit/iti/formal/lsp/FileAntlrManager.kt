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

import com.google.common.cache.CacheBuilder
import edu.kit.iti.formal.automation.parser.SyntaxErrorReporter
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.misc.ParseCancellationException
import org.eclipse.lsp4j.Diagnostic
import org.eclipse.lsp4j.DiagnosticSeverity
import org.eclipse.lsp4j.DidChangeTextDocumentParams
import org.eclipse.lsp4j.DidCloseTextDocumentParams
import org.eclipse.lsp4j.DidOpenTextDocumentParams
import org.eclipse.lsp4j.DidSaveTextDocumentParams
import org.eclipse.lsp4j.Position
import org.eclipse.lsp4j.PublishDiagnosticsParams
import org.eclipse.lsp4j.Range
import org.eclipse.lsp4j.services.TextDocumentService
import java.io.IOException
import java.time.Duration
import java.util.concurrent.CompletableFuture
import kotlin.io.path.readText

abstract class FileAntlrManager<T : ParserRuleContext>(open val server: MyLanguageServer) : TextDocumentService {
    val fileErrors = CacheBuilder.newBuilder()
        .expireAfterWrite(Duration.ofMinutes(5))
        .expireAfterAccess(Duration.ofMinutes(1))
        .maximumSize(250)
        .initialCapacity(25)
        .build<String, Exception>()
        .asMap()

    val fileCache = CacheBuilder.newBuilder()
        .expireAfterWrite(Duration.ofMinutes(5))
        .expireAfterAccess(Duration.ofMinutes(1))
        .maximumSize(250)
        .initialCapacity(25)
        .build<String, T>()
        .asMap()

    private val fileText = HashMap<String, String>()

    abstract fun parse(x: CharStream): T

    fun getSync(uri: String): T {
        if (uri !in fileCache) {
            load(uri)
        }
        return fileCache[uri]
            ?: throw (fileErrors[uri] ?: IllegalStateException("No parse result or error cached for '$uri'"))
    }

    protected fun text(uri: String): String = fileText[uri] ?: uri.toPath().readText()

    protected open fun publishDiagnostics(params: PublishDiagnosticsParams) {
        server.client.publishDiagnostics(params)
    }

    private fun parseAndPublish(uri: String) {
        try {
            getSync(uri)
            publishDiagnostics(PublishDiagnosticsParams(uri, emptyList()))
        } catch (e: SyntaxErrorReporter.ParserException) {
            publishDiagnostics(PublishDiagnosticsParams(uri, e.toDiagnostics()))
        } catch (e: ParseCancellationException) {
            publishDiagnostics(PublishDiagnosticsParams(uri, e.toDiagnostics()))
        } catch (e: IOException) {
            publishDiagnostics(
                PublishDiagnosticsParams(
                    uri,
                    listOf(
                        Diagnostic(
                            Range(Position(0, 0), Position(0, 0)),
                            e.message ?: e.toString(),
                            DiagnosticSeverity.Error,
                            "verifaps",
                        ),
                    ),
                ),
            )
        }
    }

    fun get(uri: String): CompletableFuture<T> = CompletableFuture.supplyAsync {
        try {
            getSync(uri)
        } catch (e: SyntaxErrorReporter.ParserException) {
            publishDiagnostics(PublishDiagnosticsParams(uri, e.toDiagnostics()))
            throw e
        } catch (e: ParseCancellationException) {
            publishDiagnostics(PublishDiagnosticsParams(uri, e.toDiagnostics()))
            throw e
        }
    }

    private fun load(uri: String): T? {
        try {
            val stream = fileText[uri]?.let { CharStreams.fromString(it) } ?: CharStreams.fromPath(uri.toPath())
            val ctx = parse(stream)
            fileErrors.remove(uri)
            fileCache[uri] = ctx
            return ctx
        } catch (e: SyntaxErrorReporter.ParserException) {
            fileErrors[uri] = e
            throw e
        }
    }

    private fun invalidate(uri: String) {
        fileCache.remove(uri)
        fileErrors.remove(uri)
    }

    override fun didOpen(params: DidOpenTextDocumentParams) {
        val uri = params.textDocument.uri
        fileText[uri] = params.textDocument.text
        invalidate(uri)
        parseAndPublish(uri)
    }

    override fun didChange(params: DidChangeTextDocumentParams) {
        val uri = params.textDocument.uri
        params.contentChanges.lastOrNull()?.text?.let { fileText[uri] = it }
        invalidate(uri)
        parseAndPublish(uri)
    }

    override fun didClose(params: DidCloseTextDocumentParams) {
        val uri = params.textDocument.uri
        fileText.remove(uri)
        invalidate(uri)
    }

    override fun didSave(params: DidSaveTextDocumentParams) {
        val uri = params.textDocument.uri
        params.text?.let { fileText[uri] = it }
        invalidate(uri)
        parseAndPublish(uri)
    }

//endregion
}