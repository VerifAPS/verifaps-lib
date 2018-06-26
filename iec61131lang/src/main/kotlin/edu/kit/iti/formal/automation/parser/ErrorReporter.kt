package edu.kit.iti.formal.automation.parser

import com.google.common.base.Strings
import org.antlr.v4.runtime.BaseErrorListener
import org.antlr.v4.runtime.RecognitionException
import org.antlr.v4.runtime.Recognizer
import org.antlr.v4.runtime.Token
import java.util.*
import java.util.function.Supplier

/**
 * @author Alexander Weigl
 * @version 1 (18.02.18)
 */
class ErrorReporter : BaseErrorListener() {
    var isPrint = true
    private val errors = ArrayList<SyntaxError>()

    override fun syntaxError(recognizer: Recognizer<*, *>?, offendingSymbol: Any?, line: Int,
                             charPositionInLine: Int, msg: String?, e: RecognitionException?) {
        val se = SyntaxError(
                recognizer = recognizer,
                offendingSymbol = offendingSymbol as Token?,
                source = offendingSymbol?.getTokenSource()?.getSourceName(),
                line = line,
                charPositionInLine = charPositionInLine,
                msg = msg)

        if (isPrint) {
            System.err.printf("[syntax-error] %s:%d:%d: %s%n", se.source, line, charPositionInLine, msg)
        }
        errors.add(se)
    }

    fun hasErrors(): Boolean {
        return !errors.isEmpty()
    }

    @Throws(ErrorReporter.IEC61131ParserException::class)
    fun throwException() {
        if (hasErrors())
            throw IEC61131ParserException("", errors)
    }

    @Throws(ErrorReporter.IEC61131ParserException::class)
    fun throwException(lines: Array<String>) {
        if (hasErrors()) {
            val msg = errors.joinToString(separator = "\n---\n",
                    transform = { it.getBeatifulErrorMessage(lines) })

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

    data class SyntaxError(
            val recognizer: Recognizer<*, *>? = null,
            val offendingSymbol: Token? = null,
            val line: Int = 0,
            val charPositionInLine: Int = 0,
            val msg: String? = "",
            val source: String? = null) {
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
                    .append(Strings.repeat("^", offendingSymbol?.text?.length ?: 0))
            return sb.toString()
        }

        fun positionAsUrl(): String {
            return String.format("file://source:%d", line)
        }
    }

    class IEC61131ParserException(msg: String, ts: List<SyntaxError>)
        : RuntimeException(msg) {
        val errors: List<SyntaxError> = ts

        fun print(lines: Array<String>, delimter: CharSequence): String {
            return errors
                    .map { it.getBeatifulErrorMessage(lines) }
                    .joinToString(delimter)
        }
    }
}
