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

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import org.antlr.v4.runtime.CharStream
import org.eclipse.lsp4j.DidChangeTextDocumentParams
import org.eclipse.lsp4j.DidCloseTextDocumentParams
import org.eclipse.lsp4j.DidOpenTextDocumentParams
import org.eclipse.lsp4j.InitializeParams
import org.eclipse.lsp4j.InitializeResult
import org.eclipse.lsp4j.PublishDiagnosticsParams
import org.eclipse.lsp4j.TextDocumentContentChangeEvent
import org.eclipse.lsp4j.TextDocumentIdentifier
import org.eclipse.lsp4j.TextDocumentItem
import org.eclipse.lsp4j.VersionedTextDocumentIdentifier
import org.eclipse.lsp4j.services.LanguageClient
import org.eclipse.lsp4j.services.TextDocumentService
import org.eclipse.lsp4j.services.WorkspaceService
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import java.lang.reflect.InvocationHandler
import java.lang.reflect.Method
import java.lang.reflect.Proxy
import java.nio.file.Files
import java.nio.file.Path
import java.util.concurrent.CompletableFuture

private const val VALID_ST = """
PROGRAM P
VAR
    x : INT;
END_VAR
x := 1;
END_PROGRAM
"""

private class RecordingClient : InvocationHandler {
    val published = mutableListOf<PublishDiagnosticsParams>()

    override fun invoke(proxy: Any?, method: Method, args: Array<out Any?>?): Any? {
        if (method.name == "publishDiagnostics" && args != null) {
            published.add(args[0] as PublishDiagnosticsParams)
        }
        return when {
            method.returnType == Void.TYPE -> null
            method.returnType == Boolean::class.javaPrimitiveType -> false
            else -> CompletableFuture.completedFuture(null)
        }
    }

    fun asClient(): LanguageClient = Proxy.newProxyInstance(
        LanguageClient::class.java.classLoader,
        arrayOf(LanguageClient::class.java),
        this,
    ) as LanguageClient
}

private class TestLanguageServer : MyLanguageServer() {
    override lateinit var client: LanguageClient

    override fun initialize(params: InitializeParams): CompletableFuture<InitializeResult> =
        CompletableFuture.completedFuture(InitializeResult())

    override fun getTextDocumentService(): TextDocumentService? = null

    override fun getWorkspaceService(): WorkspaceService? = null
}

private class TestAntlrManager(server: MyLanguageServer) : FileAntlrManager<IEC61131Parser.StartContext>(server) {
    override fun parse(x: CharStream): IEC61131Parser.StartContext {
        val parser = IEC61131Facade.getParser(x)
        val context = parser.start()
        parser.errorReporter.throwException()
        return context
    }
}

class FileAntlrManagerTest {
    private fun tempFile(content: String): Path =
        Files.createTempFile("lsp", ".st").also { Files.writeString(it, content) }

    private fun manager(): Pair<TestAntlrManager, RecordingClient> {
        val handler = RecordingClient()
        val server = TestLanguageServer().also { it.client = handler.asClient() }
        return TestAntlrManager(server) to handler
    }

    @Test
    fun `didOpen publishes an empty diagnostic list for valid ST`() {
        val file = tempFile(VALID_ST)
        val uri = file.toUri().toString()
        val (manager, client) = manager()

        manager.didOpen(DidOpenTextDocumentParams(TextDocumentItem(uri, "st", 1, VALID_ST)))

        assertTrue(client.published.isNotEmpty())
        assertTrue(client.published.last().diagnostics.isEmpty())
    }

    @Test
    fun `didOpen publishes diagnostics for a syntax error`() {
        val uri = tempFile("PROGRAM").toUri().toString()
        val (manager, client) = manager()

        manager.didOpen(DidOpenTextDocumentParams(TextDocumentItem(uri, "st", 1, "PROGRAM")))

        assertTrue(client.published.isNotEmpty())
        assertTrue(client.published.last().diagnostics.isNotEmpty())
    }

    @Test
    fun `didChange parses the change text, not the disk`() {
        val file = tempFile(VALID_ST)
        val uri = file.toUri().toString()
        val (manager, client) = manager()
        manager.didOpen(DidOpenTextDocumentParams(TextDocumentItem(uri, "st", 1, VALID_ST)))

        manager.didChange(
            DidChangeTextDocumentParams(
                VersionedTextDocumentIdentifier(uri, 2),
                listOf(TextDocumentContentChangeEvent("PROGRAM")),
            ),
        )

        assertTrue(client.published.last().diagnostics.isNotEmpty())
    }

    @Test
    fun `didClose removes the cached tree and errors`() {
        val file = tempFile(VALID_ST)
        val uri = file.toUri().toString()
        val (manager, _) = manager()
        manager.didOpen(DidOpenTextDocumentParams(TextDocumentItem(uri, "st", 1, VALID_ST)))
        assertTrue(manager.fileCache.containsKey(uri))

        manager.didClose(DidCloseTextDocumentParams(TextDocumentIdentifier(uri)))

        assertFalse(manager.fileCache.containsKey(uri))
        assertFalse(manager.fileErrors.containsKey(uri))
    }
}