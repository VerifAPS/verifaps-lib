package edu.kit.iti.formal.automation.st.util

import java.io.StringWriter
import java.io.Writer

/**
 *
 * CodeWriter class.
 *
 * @author weigla (15.06.2014)
 * @version 2
 */
open class CodeWriter(var stream: Writer = StringWriter())
    : Appendable by stream {

    var uppercaseKeywords = true
    var ident = "    "
    var identDepth = 0

    fun write(x: String): CodeWriter {
        stream.write(x)
        return this
    }

    fun appendIdent(): CodeWriter {
        for (i in 0 until identDepth) {
            write(ident)
        }
        return this
    }

    fun increaseIndent(): CodeWriter {
        identDepth++
        return this
    }

    fun decreaseIndent(): CodeWriter {
        identDepth = Math.max(identDepth - 1, 0)
        return this
    }

    open fun keyword(keyword: String): CodeWriter {
        return append(if (uppercaseKeywords) keyword.toUpperCase() else keyword.toLowerCase())
    }

    fun nl(): CodeWriter {
        write("\n")
        appendIdent()
        return this
    }

    fun append(vararg args: Any): CodeWriter {
        args.forEach { write(it.toString()) }
        return this
    }

    fun append(fmt: String, vararg args: Any): CodeWriter {
        return write(String.format(fmt, *args))
    }

    fun block(function: CodeWriter.() -> Unit) {
        increaseIndent()
        function()
        decreaseIndent()
    }

    fun appendReformat(text: String): CodeWriter {
        text.splitToSequence('\n').forEach { nl().append(it) }
        return this
    }
}
