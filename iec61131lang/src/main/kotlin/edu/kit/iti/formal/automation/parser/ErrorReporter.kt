package edu.kit.iti.formal.automation.parser

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2018 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import com.google.common.base.Strings
import lombok.*
import org.antlr.v4.runtime.BaseErrorListener
import org.antlr.v4.runtime.RecognitionException
import org.antlr.v4.runtime.Recognizer
import org.antlr.v4.runtime.Token

import java.util.ArrayList
import java.util.Collections
import java.util.function.Supplier
import java.util.stream.Collectors

/**
 * @author Alexander Weigl
 * @version 1 (18.02.18)
 */
class ErrorReporter : BaseErrorListener() {
    @Getter
    @Setter
    var isPrint = true
        set(print) {
            field = isPrint
        }
    @Getter
    private val errors = ArrayList<SyntaxError>()

    override fun syntaxError(recognizer: Recognizer<*, *>?, offendingSymbol: Any?, line: Int,
                             charPositionInLine: Int, msg: String?, e: RecognitionException?) {
        val se = SyntaxError.builder()
        se.recognizer = recognizer
        se.offendingSymbol = offendingSymbol as Token?
        se.source = se.offendingSymbol.getTokenSource().getSourceName()
        se.line = line
        se.charPositionInLine = charPositionInLine
        se.msg = msg
        if (isPrint) {
            System.err.printf("[syntax-error] %s:%d:%d: %s%n", se.source, line, charPositionInLine, msg)
        }
        errors.add(se.build())
    }

    fun hasErrors(): Boolean {
        return !errors.isEmpty()
    }

    @Throws(ErrorReporter.IEC61131ParserException::class)
    fun throwException() {
        if (hasErrors()) throw IEC61131ParserException(Collections.unmodifiableList(errors))
    }

    @Throws(ErrorReporter.IEC61131ParserException::class)
    fun throwException(lines: Array<String>) {
        if (hasErrors()) {
            val msg = errors.stream().map { se -> se.getBeatifulErrorMessage(lines) }.collect<String, *>(Collectors.joining("\n---\n"))
            throw IEC61131ParserException(
                    msg,
                    Collections.unmodifiableList(errors))
        }
    }

    @Throws(ErrorReporter.IEC61131ParserException::class)
    fun throwException(lines: Supplier<Array<String>>) {
        if (hasErrors()) {
            throwException(lines.get())
        }
    }

    @Value
    @Builder
    private class SyntaxError {
        val recognizer: Recognizer<*, *>
        val offendingSymbol: Token
        val line: Int = 0
        val charPositionInLine: Int = 0
        val msg: String
        val source: String? = null

        fun getBeatifulErrorMessage(lines: Array<String>): String {
            return ("syntax-error in " + positionAsUrl() + "\n"
                    + msg + "\n" + showInInput(lines) + "\n")
        }

        fun showInInput(lines: Array<String>): String {
            val line = lines[this.line]
            val sb = StringBuilder()
            sb.append(line)
                    .append("\n")
                    .append(Strings.repeat(" ", charPositionInLine - 1))
                    .append(Strings.repeat("^", offendingSymbol.text.length))
            return sb.toString()
        }

        fun positionAsUrl(): String {
            return String.format("file://source:%d", line)
        }
    }


    @Getter
    @RequiredArgsConstructor
    class IEC61131ParserException : RuntimeException {
        val errors: List<SyntaxError>

        constructor(msg: String, ts: List<SyntaxError>) : super(msg) {
            errors = ts
        }

        fun print(lines: Array<String>, delimter: CharSequence): String {
            return errors.stream().map { se -> se.getBeatifulErrorMessage(lines) }
                    .collect<String, *>(Collectors.joining(delimter))
        }
    }
}
