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
package edu.kit.iti.formal.util

import java.io.StringWriter
import java.io.Writer
import java.util.*
import kotlin.math.max

/**
 * CodeWriter class.
 *
 * @author weigla (15.06.2014)
 * @version 2
 */
open class CodeWriter(val stream: Writer = StringWriter()) : Appendable by stream {

    var uppercaseKeywords = true
    var ident = "    "
    protected var identDepth = 0

    fun write(x: String): CodeWriter {
        stream.write(x)
        return this
    }

    fun space() = write(" ")

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
        identDepth = max(identDepth - 1, 0)
        return this
    }

    open fun keyword(keyword: String): CodeWriter = printf(if (uppercaseKeywords) keyword.uppercase(Locale.getDefault()) else keyword.lowercase(Locale.getDefault()))

    fun nl(): CodeWriter {
        write("\n")
        appendIdent()
        return this
    }

    fun println(arg: String): CodeWriter = print(arg).nl()
    fun print(args: String): CodeWriter = write(args)

    fun print(vararg args: Any): CodeWriter {
        args.forEach { write(it.toString()) }
        return this
    }

    fun printf(fmt: String, vararg args: Any): CodeWriter = write(String.format(fmt, *args))

    fun block(text: String = "", nl: Boolean = false, function: CodeWriter.() -> Unit): CodeWriter {
        printf(text)
        if (nl) nl()
        increaseIndent()
        function()
        decreaseIndent()
        if (nl) nl()
        return this
    }

    fun appendReformat(text: String): CodeWriter {
        text.splitToSequence('\n').forEach { nl().printf(it) }
        return this
    }

    fun cblock(head: String, tail: String, function: CodeWriter.() -> Unit): CodeWriter {
        printf(head)
        increaseIndent()
        nl()
        function()
        decreaseIndent()
        nl()
        printf(tail)
        return this
    }

    operator fun CharSequence.unaryPlus(): CharSequence {
        this@CodeWriter.append(this@unaryPlus)
        return this@unaryPlus
    }

    open fun comment(format: String, vararg args: Any) {
        printf(format, args)
    }

    companion object {
        fun with(fn: CodeWriter.() -> Unit): String {
            val cw = CodeWriter()
            fn(cw)
            return cw.stream.toString()
        }
    }
}
