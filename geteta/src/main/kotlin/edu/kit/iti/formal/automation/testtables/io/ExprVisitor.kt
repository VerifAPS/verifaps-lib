/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
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
 */
package edu.kit.iti.formal.automation.testtables.io


import edu.kit.iti.formal.automation.testtables.exception.IllegalExpressionException
import edu.kit.iti.formal.automation.testtables.grammar.CellExpressionBaseVisitor
import edu.kit.iti.formal.automation.testtables.grammar.CellExpressionParser
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable
import edu.kit.iti.formal.smv.ast.*
import lombok.experimental.`var`
import java.util.*

/**
 * Created by weigl on 09.12.16.
 */
class ExprVisitor(private val columnVariable: SVariable, private val gtt: GeneralizedTestTable) : CellExpressionBaseVisitor<SMVExpr>() {

    override fun visitCell(ctx: CellExpressionParser.CellContext): SMVExpr {
        return ctx.chunk().map { this.visitChunk(it) }
                .reduce { a, b -> SBinaryExpression(a, SBinaryOperator.AND, b) }
    }

    override fun visitChunk(ctx: CellExpressionParser.ChunkContext): SMVExpr {
        if (ctx.constant() != null) {
            val constant = ctx.constant().accept(this)
            return constant.equal(columnVariable)
        }
        if (ctx.dontcare() != null)
            return ctx.dontcare().accept(this)
        if (ctx.interval() != null)
            return ctx.interval().accept(this)
        if (ctx.singlesided() != null)
            return ctx.singlesided().accept(this)
        if (ctx.expr() != null)
            return ctx.expr().accept(this)
        if (ctx.variable() != null) {
            val v = ctx.variable().accept(this)
            return v.equal(columnVariable)
        }
        throw IllegalStateException("No one of the N contexts matches")
    }

    override fun visitDontcare(ctx: CellExpressionParser.DontcareContext): SMVExpr {
        return SLiteral.TRUE
    }

    override fun visitConstantInt(ctx: CellExpressionParser.ConstantIntContext): SMVExpr {
        return ctx.i().accept(this)
    }

    override fun visitI(ctx: CellExpressionParser.IContext): SMVExpr {
        return SLiteral.create(java.lang.Long.parseLong(ctx.text)).`as`(columnVariable.smvType)
    }

    override fun visitConstantTrue(ctx: CellExpressionParser.ConstantTrueContext): SMVExpr {
        return SLiteral.TRUE
    }

    override fun visitConstantFalse(ctx: CellExpressionParser.ConstantFalseContext): SMVExpr {
        return SLiteral.FALSE
    }


    override fun visitSinglesided(ctx: CellExpressionParser.SinglesidedContext): SMVExpr {
        val op = ctx.relational_operator().getStart().text
        val relop = getsBinaryOperator(op)

        return columnVariable.op(relop, ctx.expr().accept(this))
    }

    private fun getsBinaryOperator(op: String): SBinaryOperator? {
        when (op) {
            "<=" -> return SBinaryOperator.LESS_EQUAL
            ">=" -> return SBinaryOperator.GREATER_EQUAL
            "<" -> return SBinaryOperator.LESS_THAN

            "=" -> return SBinaryOperator.EQUAL
            ">" -> return SBinaryOperator.GREATER_THAN
            "<>", "!=" -> return SBinaryOperator.NOT_EQUAL
        }
        return null
    }

    override fun visitInterval(ctx: CellExpressionParser.IntervalContext): SMVExpr {
        val a = ctx.lower.accept(this)
        val b = ctx.upper.accept(this)

        return SBinaryExpression(
                SBinaryExpression(a, SBinaryOperator.LESS_EQUAL, columnVariable),
                SBinaryOperator.AND,
                SBinaryExpression(columnVariable, SBinaryOperator.LESS_EQUAL, b))
    }

    override fun visitMinus(ctx: CellExpressionParser.MinusContext): SMVExpr {
        return SUnaryExpression(SUnaryOperator.MINUS, ctx.expr().accept(this))
    }


    override fun visitNegation(ctx: CellExpressionParser.NegationContext): SMVExpr {
        return SUnaryExpression(SUnaryOperator.NEGATE, ctx.expr().accept(this))
    }

    override fun visitParens(ctx: CellExpressionParser.ParensContext): SMVExpr {
        return ctx.expr().accept(this)
    }

    override fun visitCompare(ctx: CellExpressionParser.CompareContext): SMVExpr {
        val op = getsBinaryOperator(ctx.op.text)
        return SBinaryExpression(ctx.left.accept(this),
                op!!, ctx.right.accept(this))
    }

    override fun visitMod(ctx: CellExpressionParser.ModContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.MOD, ctx.right.accept(this))
    }

    override fun visitPlus(ctx: CellExpressionParser.PlusContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.PLUS, ctx.right.accept(this))
    }

    override fun visitDiv(ctx: CellExpressionParser.DivContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.DIV, ctx.right.accept(this))
    }

    override fun visitInequality(ctx: CellExpressionParser.InequalityContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.NOT_EQUAL, ctx.right.accept(this))
    }

    override fun visitSubstract(ctx: CellExpressionParser.SubstractContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.MINUS, ctx.right.accept(this))
    }

    override fun visitMult(ctx: CellExpressionParser.MultContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.MUL, ctx.right.accept(this))
    }

    override fun visitBinguardedCommand(ctx: CellExpressionParser.BinguardedCommandContext): SMVExpr {
        return ctx.guardedcommand().accept(this)
    }

    override fun visitFunctioncall(ctx: CellExpressionParser.FunctioncallContext): SMVExpr {
        //TODO call function/symbolic execution
        val args = ctx.expr().map { c -> c.accept(this) }
        return SFunction(ctx.IDENTIFIER().text,
                *args.toTypedArray())
    }

    override fun visitBvariable(ctx: CellExpressionParser.BvariableContext): SMVExpr {
        return ctx.variable().accept(this)
    }

    override fun visitVariable(ctx: CellExpressionParser.VariableContext): SMVExpr {
        val varText = ctx.IDENTIFIER().text
        val isReference = ctx.RBRACKET() != null

        return if (gtt.isVariable(varText)) {
            val variable = gtt.getSMVVariable(varText)
            if (isReference)
                gtt.getReference(variable, Integer.parseInt(ctx.i().text))
            else
                variable
        } else {
            if (isReference)
                throw IllegalExpressionException("You referenced a variable $varText, but it is not found as a defined io-variable.")
            SLiteral(ENUM_TYPE, varText)
        }
    }

    override fun visitLogicalAnd(ctx: CellExpressionParser.LogicalAndContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.AND, ctx.right.accept(this))
    }

    override fun visitLogicalXor(ctx: CellExpressionParser.LogicalXorContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.XOR, ctx.right.accept(this))
    }

    override fun visitBconstant(ctx: CellExpressionParser.BconstantContext): SMVExpr {
        return ctx.constant().accept(this)
    }

    override fun visitLogicalOr(ctx: CellExpressionParser.LogicalOrContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.OR, ctx.right.accept(this))
    }

    override fun visitEquality(ctx: CellExpressionParser.EqualityContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.EQUAL, ctx.right.accept(this))
    }

    override fun visitGuardedcommand(ctx: CellExpressionParser.GuardedcommandContext): SMVExpr {
        val c = SCaseExpression()
        try {
            var i = 0
            while (true) {
                val g = ctx.expr(i).accept(this)
                val t = ctx.expr(i + 1).accept(this)
                c.addCase(g, t)
                i += 2
            }
        } catch (npe: NullPointerException) {
        }

        return c
    }

    companion object {
        private val ENUM_TYPE = SMVType.EnumType(LinkedList())
    }
}
