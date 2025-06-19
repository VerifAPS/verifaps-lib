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
package edu.kit.iti.formal.smt

import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import org.antlr.v4.runtime.ConsoleErrorListener
import org.antlr.v4.runtime.RecognitionException
import org.antlr.v4.runtime.Recognizer
import java.math.BigInteger

/**
 *
 * @author Alexander Weigl
 * @version 1 (11.12.18)
 */
object SExprFacade {
    fun createParser(stream: CharStream): SexprParser {
        val lexer = SexprLexer(stream)
        val parser = SexprParser(CommonTokenStream(lexer))
        return parser
    }

    fun createParser(stream: String) = createParser(CharStreams.fromString(stream))

    /**
     * Parse the given input as a list of sexpr.
     */
    fun parse(stream: CharStream): List<SExpr> {
        val p = createParser(stream)
        val ctx = p.file()
        val t = SexprParseTreeTransformer()
        val ast = ctx.accept(t) as SList
        return ast.list
    }

    fun parseExpr(stream: CharStream): SExpr {
        val p = createParser(stream)
        p.removeErrorListeners()
        p.addErrorListener(object : ConsoleErrorListener() {
            override fun syntaxError(
                recognizer: Recognizer<*, *>?,
                offendingSymbol: Any?,
                line: Int,
                charPositionInLine: Int,
                msg: String?,
                e: RecognitionException?,
            ) {
                super.syntaxError(recognizer, offendingSymbol, line, charPositionInLine, msg, e)
                throw IllegalArgumentException("Syntax error at line $line:$charPositionInLine $msg")
            }
        })
        val ctx = p.sexpr()
        val t = SexprParseTreeTransformer()
        return ctx.accept(t)
    }

    fun parseExpr(stream: String): SExpr = parseExpr(CharStreams.fromString(stream))

    fun sexpr(vararg args: Any) = sexpr(args.toList())

    fun sexpr(args: Collection<Any>): SList {
        val s = SList()
        args.forEach {
            s.list += when (it) {
                is SExpr -> it
                is String -> SSymbol(it)
                is Int -> SNumber(BigInteger.valueOf(it.toLong()))
                is Collection<*> -> sexpr(it)
                // is Float -> SNumber(it)
                else -> {
                    SSymbol("${it.javaClass} not supported")
                }
            }
        }
        return s
    }

    fun fnapply(name: String, args: List<SExpr>) = SList(name).also { it.addAll(args) }

    fun notEquals(left: SExpr, right: SExpr): SExpr = SList("not", SList("=", left, right))
}