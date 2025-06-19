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
package edu.kit.iti.formal.automation

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.main
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.multiple
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import edu.kit.iti.formal.automation.analysis.ReportCategory
import edu.kit.iti.formal.automation.analysis.ReportLevel
import edu.kit.iti.formal.automation.analysis.Reporter
import edu.kit.iti.formal.automation.analysis.ReporterMessage
import edu.kit.iti.formal.automation.builtin.BuiltinLoader
import edu.kit.iti.formal.automation.parser.IEC61131Lexer
import edu.kit.iti.formal.automation.parser.IEC61131Parser
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST
import edu.kit.iti.formal.automation.st.ast.PouElements
import edu.kit.iti.formal.util.info
import org.antlr.v4.runtime.*
import org.antlr.v4.runtime.atn.ATNConfigSet
import org.antlr.v4.runtime.dfa.DFA
import java.io.File
import java.util.*

object Check {
    @JvmStatic
    fun main(args: Array<String>) = CheckApp().main(args)
}

object Flycheck {
    @JvmStatic
    fun main(args: Array<String>) {
        // println("{version:\"0.9\"}")
        val reader = System.`in`.bufferedReader()
        do {
            val line = reader.readLine() ?: break
            if (line.isEmpty()) continue
            CheckApp().main(parseArgs(line))
        } while (true)
    }

    /**
     * from https://stackoverflow.com/questions/1082953/shlex-alternative-for-java
     * license. unlicense/public domain
     */
    @JvmStatic
    fun parseArgs(argString: CharSequence): List<String> {
        val tokens = ArrayList<String>()
        var escaping = false
        var quoteChar = ' '
        var quoting = false
        var current = StringBuilder()
        for (i in 0 until argString.length) {
            val c = argString[i]
            if (escaping) {
                current.append(c)
                escaping = false
            } else if (c == '\\' && !(quoting && quoteChar == '\'')) {
                escaping = true
            } else if (quoting && c == quoteChar) {
                quoting = false
            } else if (!quoting && (c == '\'' || c == '"')) {
                quoting = true
                quoteChar = c
            } else if (!quoting && Character.isWhitespace(c)) {
                if (current.length > 0) {
                    tokens.add(current.toString())
                    current = StringBuilder()
                }
            } else {
                current.append(c)
            }
        }
        if (current.isNotEmpty()) {
            tokens.add(current.toString())
        }
        return tokens
    }
}

class CheckApp : CliktCommand() {
    val verbose by option(help = "enable verbose mode").flag()
    val format by option("--json", help = "Flag for enabling json, line based format").flag()
    val include by option("-L", help = "folder for looking includes")
        .file()
        .multiple()

    val includeBuiltIn by option("-b", help = "")
        .flag("-B")

    val files by argument(name = "FILE", help = "Files to check")
        .file()
        .multiple()

    override fun run() {
        val base = if (includeBuiltIn) BuiltinLoader.loadDefault() else PouElements()

        val r = FlycheckRunner(
            files.map { CharStreams.fromFileName(it.absolutePath) },
            base,
            verbose,
            format,
            include,
        )
        r.run()
    }
}

class FlycheckRunner(
    val streams: List<CharStream>,
    val library: PouElements = PouElements(),
    val verbose: Boolean = false,
    val json: Boolean = false,
    val includeStubs: List<File> = arrayListOf(),
) {

    val underInvestigation: PouElements = PouElements()

    private val reporter = Reporter()
    val messages: MutableList<ReporterMessage>
        get() = reporter.messages

    private val errorListener = MyAntlrErrorListener(reporter)

    fun run() {
        info("Start with parsing")
        streams.forEach { parse(it) }
        info("Resolving...")
        resolve()
        info("Checking...")
        check()
        info("Print.")
        printMessages()
    }

    fun parse(stream: CharStream) {
        val lexer = IEC61131Lexer(stream)
        val parser = IEC61131Parser(CommonTokenStream(lexer))

        lexer.removeErrorListeners()
        parser.removeErrorListeners()
        parser.addErrorListener(errorListener)
        val ctx = parser.start()
        val tles = ctx.accept(IECParseTreeToAST()) as PouElements
        library.addAll(tles)
        underInvestigation.addAll(tles)
    }

    private fun resolve() {
        IEC61131Facade.resolveDataTypes(library)
    }

    fun check() {
        messages.addAll(IEC61131Facade.check(underInvestigation))
    }

    private fun printMessages() {
        if (messages.isEmpty()) {
            if (json) {
                println("{ok:true}")
            } else {
                info("Everything is fine.")
            }
        } else {
            if (json) {
                val msg = messages.joinToString(",") { it.toJson() }
                print("[$msg]\n")
                System.out.flush()
            } else {
                messages.forEach { info(it.toHuman()) }
            }
        }
    }

    private fun printMessage(message: ReporterMessage) {
    }

    class MyAntlrErrorListener(private val reporter: Reporter) : ANTLRErrorListener {
        override fun syntaxError(
            recognizer: Recognizer<*, *>?,
            offendingSymbol: Any?,
            line: Int,
            charPositionInLine: Int,
            msg: String?,
            e: RecognitionException?,
        ) {
            val token = (offendingSymbol as Token)
            reporter.report(
                token,
                msg!!,
                ReportCategory.SYNTAX,
                ReportLevel.ERROR,
            )
        }

        override fun reportAttemptingFullContext(recognizer: Parser?, dfa: DFA?, startIndex: Int, stopIndex: Int, conflictingAlts: BitSet?, configs: ATNConfigSet?) {}
        override fun reportAmbiguity(recognizer: Parser?, dfa: DFA?, startIndex: Int, stopIndex: Int, exact: Boolean, ambigAlts: BitSet?, configs: ATNConfigSet?) {}
        override fun reportContextSensitivity(recognizer: Parser?, dfa: DFA?, startIndex: Int, stopIndex: Int, prediction: Int, configs: ATNConfigSet?) {}
    }
}
