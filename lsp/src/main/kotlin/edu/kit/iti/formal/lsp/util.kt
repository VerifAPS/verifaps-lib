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

import edu.kit.iti.formal.automation.parser.SyntaxErrorReporter
import org.antlr.v4.runtime.Lexer
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.Token
import org.antlr.v4.runtime.misc.ParseCancellationException
import org.antlr.v4.runtime.tree.ParseTree
import org.antlr.v4.runtime.tree.TerminalNode
import org.eclipse.lsp4j.Diagnostic
import org.eclipse.lsp4j.DiagnosticSeverity
import org.eclipse.lsp4j.Position
import org.eclipse.lsp4j.Range
import java.nio.file.Path
import java.nio.file.Paths
import kotlin.math.max
import kotlin.math.min
import kotlin.text.substring

fun String.toPath(): Path = Paths.get(this.replace("file://", ""))

internal fun String.substring(startIndex: Position, endIndex: Position): String {
    var start: Int = -1
    var end: Int = -1
    var currentLine = 0
    for ((index, ch) in this.withIndex()) {
        if (ch == '\n') currentLine++
        if (startIndex.line == currentLine) {
            start = index + startIndex.character
        }
        if (endIndex.line == currentLine) {
            end = index + endIndex.character
        }
        if (start != -1 && end != -1) break
    }
    return substring(min(start, end), max(start, end))
}

internal operator fun ParseTree.contains(position: Position): Boolean =
    when (this) {
        is ParserRuleContext -> start <= position && position <= stop
        is TerminalNode -> symbol <= position && position <= symbol
        else -> false
    }

internal operator fun Pair<Int, Int>.compareTo(o: Pair<Int, Int>): Int {
    val (a, b) = this
    val (x, y) = o

    val q = a - x
    if (q != 0) {
        return q
    }
    return b - y
}

internal operator fun Token.compareTo(position: Position): Int =
    (line to charPositionInLine).compareTo(position.line to position.character)

internal operator fun Position.compareTo(tok: Token): Int {
    val x = line - tok.line
    if (x != 0) return x
    return character - tok.charPositionInLine
}

internal fun SyntaxErrorReporter.ParserException.toDiagnostics(): List<Diagnostic> = errors.map {
    Diagnostic(
        it.location.toRange,
        it.message,
        DiagnosticSeverity.Error,
        "KeY-Parser"
    )
}

fun ParseCancellationException.toDiagnostics(): List<Diagnostic> = listOf(
    Diagnostic(
        Range(Position(0, 0), Position(0, 0)), // TODO
        message ?: (" " + this),
        DiagnosticSeverity.Error,
        "KeY-Parser"
    )
)

internal fun String.substring(range: Range) = substring(range.start, range.end)

internal fun String.findLastPosition(): Position {
    val line = count { it == '\n' }
    val column = if (line == 0) {
        length
    } else {
        length - lastIndexOf('\n')
    }
    return Position(line, column)
}

internal fun String.indexOf(position: Position): Int {
    var currentLine = 0
    for ((index, ch) in withIndex()) {
        if (ch == '\n') currentLine++
        if (position.line == currentLine) {
            return index + position.character
        }
    }
    return -1
}

fun Lexer.asSequence(): Sequence<Token> = sequence {
    var token: Token
    do {
        token = nextToken()
        yield(token)
    } while (token.type > 0)
}