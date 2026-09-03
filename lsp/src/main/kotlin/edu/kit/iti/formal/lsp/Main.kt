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

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.main
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.enum
import com.github.ajalt.clikt.parameters.types.int
import edu.kit.iti.formal.lsp.gtt.GttLanguageServer
import edu.kit.iti.formal.lsp.smv.SmvLanguageServer
import edu.kit.iti.formal.lsp.st.StructuredTextLanguageServer
import org.eclipse.lsp4j.launch.LSPLauncher
import org.eclipse.lsp4j.services.LanguageClient
import org.slf4j.LoggerFactory
import java.io.InputStream
import java.io.OutputStream
import java.io.PrintWriter
import java.net.InetAddress
import java.net.ServerSocket
import java.net.Socket
import java.util.concurrent.ExecutorService
import java.util.concurrent.ForkJoinPool
import java.util.concurrent.Future
import kotlin.concurrent.thread

/**
 * Main entry point for the VerifAPS LSP servers.
 * Supports three languages: GTT, StructuredText, and SMV.
 * 
 * @author Alexander Weigl (adapted)
 * @version 1.0
 */
object Main {
    @JvmStatic
    fun main(args: Array<String>) {
        VerifapsLspCommand().main(args)
    }
}

val executorService: ExecutorService = ForkJoinPool.commonPool()
private val LOGGER = LoggerFactory.getLogger("verifaps-lsp")

enum class Language {
    GTT,
    STRUCTURED_TEXT,
    SMV
}

class VerifapsLspCommand : CliktCommand("VerifAPS Language Server") {
    private val traceEnabled by option("--trace", help = "Enable tracing (file path or '-' for stderr)")
    private val stdioMode by option("--stdio", help = "Use standard I/O for communication").flag()
    private val serverMode by option("--server", help = "Run as TCP server on specified port").int()
    private val clientMode by option("--client", help = "Connect as TCP client to specified port").int()
    private val language by option(
        "--language",
        help = "Language to serve: gtt, st, smv (default: auto-detect)"
    ).enum<Language>().default(Language.STRUCTURED_TEXT)

    override fun run() {
        try {
            when {
                stdioMode -> launchLanguageServer(System.`in`, System.out).get()
                serverMode != null -> runAsServer(serverMode!!)
                clientMode != null -> runAsClient(clientMode!!)
                else -> launchLanguageServer(System.`in`, System.out).get()
            }
        } catch (e: Exception) {
            LOGGER.error("Error at starting LSP server", e)
        }
    }

    private fun launchLanguageServer(input: InputStream, output: OutputStream): Future<*> {
        val ls = when (language) {
            Language.GTT -> GttLanguageServer()
            Language.STRUCTURED_TEXT -> StructuredTextLanguageServer()
            Language.SMV -> SmvLanguageServer()
        }

        val launcher = LSPLauncher.Builder<LanguageClient>()
            .setLocalService(ls)
            .setRemoteInterface(LanguageClient::class.java)
            .setInput(input)
            .setOutput(output)
            .setExecutorService(executorService)
            .validateMessages(true)
            .configureGson { }
            .setClassLoader(javaClass.classLoader)

        traceEnabled?.let {
            LOGGER.info("Tracing enabled: $it")
            if (it == "-") {
                launcher.traceMessages(PrintWriter(System.err))
            } else {
                launcher.traceMessages(PrintWriter(it))
            }
        }

        val l = launcher.create()
        ls.client = l.remoteProxy
        return l.startListening()
    }

    private fun runAsClient(port: Int) {
        val socket = Socket("localhost", port)
        socket.tcpNoDelay = true
        socket.keepAlive = true
        launchLanguageServer(socket.getInputStream(), socket.getOutputStream()).get()
    }

    private fun runAsServer(port: Int) {
        try {
            ServerSocket(port, 1, InetAddress.getLoopbackAddress()).use { serverSocket ->
                while (true) {
                    LOGGER.info("Listening on {}", serverSocket.localSocketAddress)
                    val socket = serverSocket.accept()
                    socket.tcpNoDelay = true
                    socket.keepAlive = true
                    thread(start = true, isDaemon = true, name = "connection-worker") {
                        launchLanguageServer(socket.getInputStream(), socket.getOutputStream()).get()
                    }
                }
            }
        } catch (e: Exception) {
            LOGGER.error("", e)
        }
    }
}