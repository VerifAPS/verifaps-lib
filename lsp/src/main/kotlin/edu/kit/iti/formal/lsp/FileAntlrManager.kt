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
import org.eclipse.lsp4j.DidChangeTextDocumentParams
import org.eclipse.lsp4j.DidCloseTextDocumentParams
import org.eclipse.lsp4j.DidOpenTextDocumentParams
import org.eclipse.lsp4j.DidSaveTextDocumentParams
import org.eclipse.lsp4j.PublishDiagnosticsParams
import org.eclipse.lsp4j.services.TextDocumentService
import java.time.Duration
import java.util.concurrent.CompletableFuture

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

    abstract fun parse(x: CharStream): T

    fun getSync(uri: String): T {
        if (uri !in fileCache) {
            load(uri)
        }
        return fileCache[uri] ?: throw fileErrors[uri]!!
    }

    fun get(uri: String): CompletableFuture<T> = CompletableFuture.supplyAsync {
        try {
            getSync(uri)
        } catch (e: SyntaxErrorReporter.ParserException) {
            server.client.publishDiagnostics(
                PublishDiagnosticsParams(uri, e.toDiagnostics())
            )
            throw e
        } catch (e: ParseCancellationException) {
            server.client.publishDiagnostics(
                PublishDiagnosticsParams(uri, e.toDiagnostics())
            )
            throw e
        }
    }

    private fun load(uri: String): T? {
        val path = uri.toPath()
        try {
            val ctx = parse(CharStreams.fromPath(path))
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
    }

    override fun didOpen(params: DidOpenTextDocumentParams) {
        // read in, in advance
        getSync(params.textDocument.uri)
    }

    override fun didChange(params: DidChangeTextDocumentParams) {
        invalidate(params.textDocument.uri)
    }

    override fun didClose(params: DidCloseTextDocumentParams) {
        // Nothing to do
    }

    override fun didSave(params: DidSaveTextDocumentParams) {
        invalidate(params.textDocument.uri)
        getSync(params.textDocument.uri)
    }

//endregion
}