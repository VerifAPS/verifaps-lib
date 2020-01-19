package edu.kit.iti.formal.automation.parser

import edu.kit.iti.formal.util.times
import org.antlr.v4.runtime.*
import java.util.*
import java.util.function.Supplier

/**
 * @author Alexander Weigl
 * @version 1 (18.02.18)
 */
class SyntaxErrorReporter : BaseErrorListener() {
    var isPrint = true
    private val errors = ArrayList<SyntaxError>()

    override fun syntaxError(recognizer: Recognizer<*, *>?, offendingSymbol: Any?, line: Int,
                             charPositionInLine: Int, msg: String?, e: RecognitionException?) {

        val parser = recognizer as? Parser
        val stack = parser?.ruleInvocationStack?.joinToString(", ")

        val se = SyntaxError(
                recognizer = recognizer,
                offendingSymbol = offendingSymbol as Token?,
                source = offendingSymbol?.getTokenSource()?.getSourceName(),
                line = line,
                charPositionInLine = charPositionInLine,
                msg = msg, stack = stack ?: "")

        if (isPrint) {
            System.err.printf("[syntax-error] %s:%d:%d: %s (%s)%n", se.source, line, charPositionInLine, msg, stack)
        }
        errors.add(se)
    }

    fun hasErrors(): Boolean {
        return !errors.isEmpty()
    }

    @Throws(SyntaxErrorReporter.ParserException::class)
    fun throwException() {
        if (hasErrors())
            throw ParserException("", errors)
    }

    @Throws(SyntaxErrorReporter.ParserException::class)
    fun throwException(lines: Array<String>) {
        if (hasErrors()) {
            val msg = errors.joinToString(separator = "\n---\n",
                    transform = { it.getBeatifulErrorMessage(lines) })

            throw ParserException(
                    msg,
                    Collections.unmodifiableList(errors))
        }
    }

    @Throws(SyntaxErrorReporter.ParserException::class)
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
            val source: String? = null,
            val stack: String) {
        fun getBeatifulErrorMessage(lines: Array<String>): String {
            return ("syntax-error in " + positionAsUrl() + "\n"
                    + msg + "\n" + showInInput(lines) + "\n")
        }

        fun showInInput(lines: Array<String>): String {
            val line = lines[this.line]
            val sb = StringBuilder()
            sb.append(line)
                    .append("\n")
                    .append(" " * (charPositionInLine - 1))
                    .append("^" * (offendingSymbol?.text?.length ?: 0))
            return sb.toString()
        }

        fun positionAsUrl(): String {
            return String.format("file://source:%d", line)
        }
    }

    class ParserException(msg: String, ts: List<SyntaxError>)
        : RuntimeException(msg) {
        val errors: List<SyntaxError> = ts

        fun print(lines: Array<String>, delimter: CharSequence): String {
            return errors
                    .map { it.getBeatifulErrorMessage(lines) }
                    .joinToString(delimter)
        }
    }
}
