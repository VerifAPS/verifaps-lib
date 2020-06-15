package edu.kit.iti.formal.smv

/*-
 * #%L
 * smv-model
 * %%
 * Copyright (C) 2016 Alexander Weigl
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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.smv.parser.SMVLexer
import edu.kit.iti.formal.smv.parser.SMVParser
import edu.kit.iti.formal.smv.parser.SMVTransformToAST
import org.antlr.v4.runtime.CharStream
import org.antlr.v4.runtime.CharStreams
import org.antlr.v4.runtime.CommonTokenStream
import java.util.*
import java.util.function.BinaryOperator
import java.util.regex.Pattern

/**
 * Created by weigl on 26.11.16.
 */
object SMVFacade {
    val FUNCTION_ID_RESIZE = "resize"
    val FUNCTION_ID_EXPAND = "expand"
    val FUNCTION_ID_BIT_ACCESS = "<bitaccess>"

    @JvmStatic
    fun getFunction1(name: String): SFunction {
        val f = SFunction(name)
        f.typeSolver = FunctionTypeSolvers.FIRST_ARGUMENT
        return f
    }

    @JvmStatic
    fun next(expr: SMVExpr): SMVExpr {
        return SFunction("next", expr)
    }

    @JvmStatic
    fun caseexpr(vararg exprs: SMVExpr): SMVExpr {
        val e = SCaseExpression()
        var i = 0
        while (i < exprs.size) {
            e.addCase(exprs[i], exprs[i + 1])
            i += 2
        }
        return e
    }


    @JvmStatic
    fun combine(op: SBinaryOperator, vararg exprs: SMVExpr): SMVExpr {
        return Arrays.stream(exprs).reduce(reducer(op)).get()
    }

    @JvmStatic
    fun combine(op: SBinaryOperator, exprs: List<SMVExpr>): SMVExpr {
        return exprs.stream().reduce(reducer(op)).get()
    }

    @JvmStatic
    fun combine(op: SBinaryOperator, exprs: List<SMVExpr>, defaultValue: SMVExpr): SMVExpr {
        return exprs.stream().reduce(reducer(op)).orElse(defaultValue)
    }

    @JvmStatic
    fun reducer(op: SBinaryOperator): BinaryOperator<SMVExpr> {
        return BinaryOperator({ a: SMVExpr, b: SMVExpr -> SBinaryExpression(a, op, b) })
    }

    @JvmStatic
    fun reducerKt(op: SBinaryOperator): (SMVExpr, SMVExpr) -> SMVExpr =
            { a: SMVExpr, b: SMVExpr -> SBinaryExpression(a, op, b) }


    @JvmStatic
    fun NOT(e: SMVExpr): SUnaryExpression {
        return SUnaryExpression(SUnaryOperator.NEGATE, e)
    }

    fun expr(s: String): SMVExpr {
        val ctx = getParser(CharStreams.fromString(s)).exprEOF()
        return ctx.accept(SMVTransformToAST()) as SMVExpr
    }

    /*
    public static CaseExpression makeIfThenElse(Expression cond, Expression thenExpr, Expression elseExpr) {
        CaseExpression result = new CaseExpression();
        result.addCase(cond, thenExpr);
        result.setElseExpression(elseExpr);
        return result;
    }
*/
    fun wordConcat(a: SMVExpr, b: SMVExpr) = a.wordConcat(b)

    fun expand(expr: SMVExpr, sz: SLiteral): SMVExpr =
            SFunction(FUNCTION_ID_EXPAND, expr, sz)

    fun resize(expr: SMVExpr, sz: SLiteral): SMVExpr =
            SFunction(FUNCTION_ID_RESIZE, expr, sz)

    fun bitAccess(expr: SMVExpr, from: SLiteral, to: SLiteral) =
            SFunction(FUNCTION_ID_BIT_ACCESS, from, to)

    fun bitAccess(expr: SMVExpr, from: Long, to: Long) =
            bitAccess(expr, SLiteral.integer(from), SLiteral.integer(to))

    fun getParser(stream: CharStream): SMVParser {
        return SMVParser(CommonTokenStream(SMVLexer(stream)))
    }

    val PATTERN_WORD_LITERAL = Pattern.compile("0([us])([dxo])(\\d+)_(\\d+)")

    fun isWordLiteral(text: String): Boolean {
        val m = PATTERN_WORD_LITERAL.matcher(text)
        return m.matches()
    }

    fun parseWordLiteral(text: String): SWordLiteral {
        val m = PATTERN_WORD_LITERAL.matcher(text)
        if (m.matches()) {
            val signed = m.group(1) == "s"
            val ord = when (m.group(2)) {
                "x" -> 16
                "o" -> 8
                else -> 10
            }
            val digits = m.group(3).toInt()
            val value = m.group(4).toBigInteger(ord)
            return SWordLiteral(value, SMVWordType(signed, digits))
        }
        throw IllegalArgumentException()
    }
}

