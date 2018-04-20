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

/**
 * Created by weigl on 26.11.16.
 */
object SMVFacade {
    val FUNCTION_ID_RESIZE = "resize"
    val FUNCTION_ID_EXPAND = "expand"
    val FUNCTION_ID_BIT_ACCESS = "<bitaccess>"

    fun getFunction1(name: String): SFunction {
        val f = SFunction(name)
        f.typeSolver = FunctionTypeSolvers.FIRST_ARGUMENT
        return f
    }

    fun next(expr: SMVExpr): SMVExpr {
        return SFunction("next", expr)
    }


    fun caseexpr(vararg exprs: SMVExpr): SMVExpr {
        val e = SCaseExpression()
        var i = 0
        while (i < exprs.size) {
            e.addCase(exprs[i], exprs[i + 1])
            i += 2
        }
        return e
    }


    fun combine(op: SBinaryOperator, vararg exprs: SMVExpr): SMVExpr {
        return Arrays.stream(exprs).reduce(reducer(op)).get()
    }

    fun combine(op: SBinaryOperator, exprs: List<SMVExpr>): SMVExpr {
        return exprs.stream().reduce(reducer(op)).get()
    }

    fun combine(op: SBinaryOperator, exprs: List<SMVExpr>, defaultValue: SMVExpr): SMVExpr {
        return exprs.stream().reduce(reducer(op)).orElse(defaultValue)
    }

    fun reducer(op: SBinaryOperator): (SMVExpr, SMVExpr) -> SMVExpr {
        return { a: SMVExpr, b: SMVExpr -> SBinaryExpression(a, op, b) }
    }

    fun reducerFn(op: SBinaryOperator): BinaryOperator<SMVExpr> {
        return BinaryOperator({ a: SMVExpr, b: SMVExpr -> SBinaryExpression(a, op, b) })
    }

    fun NOT(e: SMVExpr): SUnaryExpression {
        return SUnaryExpression(SUnaryOperator.NEGATE, e)
    }

    fun expr(s: String): SMVExpr {
        val ctx = getParser(CharStreams.fromString(s)).expr()
        return ctx.accept(SMVTransformToAST()) as SMVExpr
    }

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
}

