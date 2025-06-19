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
package edu.kit.iti.formal.automation.testtables.io

import edu.kit.iti.formal.automation.testtables.exception.IllegalExpressionException
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParserBaseVisitor
import edu.kit.iti.formal.automation.testtables.model.ParseContext
import edu.kit.iti.formal.smv.EnumType
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.SMVWordType
import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.util.fail
import org.antlr.v4.runtime.tree.TerminalNode
import java.util.*

/**
 * Created by weigl on 09.12.16.
 */
class TblLanguageToSmv(
    private val columnVariable: SVariable,
    private val columnProgramRun: Int = 0,
    private val context: ParseContext,
) : TestTableLanguageParserBaseVisitor<SMVExpr>() {

    override fun visitCell(ctx: TestTableLanguageParser.CellContext): SMVExpr = ctx.chunk().map { it.accept(this) }
        .reduce { a, b -> SBinaryExpression(a, SBinaryOperator.AND, b) }

    override fun visitCconstant(ctx: TestTableLanguageParser.CconstantContext): SMVExpr {
        val constant = ctx.constant().accept(this)
        return constant.equal(columnVariable)
    }

    override fun visitDontcare(ctx: TestTableLanguageParser.DontcareContext): SMVExpr = SLiteral.TRUE

    override fun visitCvariable(ctx: TestTableLanguageParser.CvariableContext): SMVExpr =
        ctx.variable().accept(this).equal(columnVariable)

    override fun visitConstantInt(ctx: TestTableLanguageParser.ConstantIntContext): SMVExpr = ctx.i().accept(this)

    override fun visitI(ctx: TestTableLanguageParser.IContext): SMVExpr {
        val text = ctx.text
        if (SMVFacade.isWordLiteral(text)) {
            return SMVFacade.parseWordLiteral(text)
        } else {
            val value = ctx.text.toBigInteger()
            if (columnVariable.dataType == SMVTypes.INT) {
                return SIntegerLiteral(value)
            } else {
                val dtWord = (columnVariable.dataType as? SMVWordType?)
                return SWordLiteral(value, dtWord ?: SMVTypes.signed(16))
            }
        }
    }

    override fun visitConstantTrue(ctx: TestTableLanguageParser.ConstantTrueContext): SMVExpr = SLiteral.TRUE

    override fun visitConstantFalse(ctx: TestTableLanguageParser.ConstantFalseContext): SMVExpr = SLiteral.FALSE

    override fun visitSinglesided(ctx: TestTableLanguageParser.SinglesidedContext): SMVExpr {
        val op = ctx.relational_operator().getStart().text
        val relop = getsBinaryOperator(op)

        return columnVariable.op(relop, ctx.expr().accept(this))
    }

    private fun getsBinaryOperator(op: String): SBinaryOperator {
        when (op) {
            "<=" -> return SBinaryOperator.LESS_EQUAL
            ">=" -> return SBinaryOperator.GREATER_EQUAL
            "<" -> return SBinaryOperator.LESS_THAN

            "=" -> return SBinaryOperator.EQUAL
            ">" -> return SBinaryOperator.GREATER_THAN
            "<>", "!=" -> return SBinaryOperator.NOT_EQUAL
        }
        throw IllegalStateException("$op not found as an binary operator for SMV")
    }

    override fun visitInterval(ctx: TestTableLanguageParser.IntervalContext): SMVExpr {
        val a = ctx.lower.accept(this)
        val b = ctx.upper.accept(this)

        return SBinaryExpression(
            SBinaryExpression(a, SBinaryOperator.LESS_EQUAL, columnVariable),
            SBinaryOperator.AND,
            SBinaryExpression(columnVariable, SBinaryOperator.LESS_EQUAL, b),
        )
    }

    override fun visitMinus(ctx: TestTableLanguageParser.MinusContext): SMVExpr =
        SUnaryExpression(SUnaryOperator.MINUS, ctx.expr().accept(this))

    override fun visitNegation(ctx: TestTableLanguageParser.NegationContext): SMVExpr =
        SUnaryExpression(SUnaryOperator.NEGATE, ctx.expr().accept(this))

    override fun visitParens(ctx: TestTableLanguageParser.ParensContext): SMVExpr = ctx.expr().accept(this)

    override fun visitCompare(ctx: TestTableLanguageParser.CompareContext): SMVExpr {
        val op = getsBinaryOperator(ctx.op.text)
        return SBinaryExpression(
            ctx.left.accept(this),
            op,
            ctx.right.accept(this),
        )
    }

    override fun visitMod(ctx: TestTableLanguageParser.ModContext): SMVExpr =
        SBinaryExpression(ctx.left.accept(this), SBinaryOperator.MOD, ctx.right.accept(this))

    override fun visitPlus(ctx: TestTableLanguageParser.PlusContext): SMVExpr =
        SBinaryExpression(ctx.left.accept(this), SBinaryOperator.PLUS, ctx.right.accept(this))

    override fun visitDiv(ctx: TestTableLanguageParser.DivContext): SMVExpr =
        SBinaryExpression(ctx.left.accept(this), SBinaryOperator.DIV, ctx.right.accept(this))

    override fun visitInequality(ctx: TestTableLanguageParser.InequalityContext): SMVExpr =
        SBinaryExpression(ctx.left.accept(this), SBinaryOperator.NOT_EQUAL, ctx.right.accept(this))

    override fun visitSubstract(ctx: TestTableLanguageParser.SubstractContext): SMVExpr =
        SBinaryExpression(ctx.left.accept(this), SBinaryOperator.MINUS, ctx.right.accept(this))

    override fun visitMult(ctx: TestTableLanguageParser.MultContext): SMVExpr =
        SBinaryExpression(ctx.left.accept(this), SBinaryOperator.MUL, ctx.right.accept(this))

    override fun visitBinguardedCommand(ctx: TestTableLanguageParser.BinguardedCommandContext): SMVExpr =
        ctx.guardedcommand().accept(this)

    override fun visitFunctioncall(ctx: TestTableLanguageParser.FunctioncallContext): SMVExpr {
        // TODO call function/symbolic execution
        val args = ctx.expr().map { c -> c.accept(this) }
        return SFunction(
            ctx.IDENTIFIER().text,
            *args.toTypedArray(),
        )
    }

    override fun visitBvariable(ctx: TestTableLanguageParser.BvariableContext): SMVExpr = ctx.variable().accept(this)

    /*override fun visitEnum(ctx: TestTableLanguageParser.EnumContext): SMVExpr {
        return SEnumLiteral(ctx.text)
    }*/

    private fun resolveName(identifier: TerminalNode?, fqVariable: TerminalNode?): Pair<Int, String> {
        if (fqVariable != null) {
            require(context.relational) {
                "Full-qualified variable used in non-relational test table."
            }

            val parts = fqVariable.text.split("|>", "·", "::", limit = 2)
            val name = if (parts[1].isEmpty()) columnVariable.name else parts[1]
            val runNum =
                if (parts[0].isEmpty()) {
                    1 - columnProgramRun
                } else {
                    parts[0].toIntOrNull() ?: context.programRuns.indexOf(parts[0])
                }
            require(runNum >= 0)
            return runNum to name
        }
        if (identifier != null) {
            return columnProgramRun to identifier.text
        }
        fail("")
    }

    override fun visitVariable(ctx: TestTableLanguageParser.VariableContext): SMVExpr {
        val (programRun, varText) = resolveName(ctx.IDENTIFIER(), ctx.FQ_VARIABLE())
        val isReference = ctx.RBRACKET() != null

        return if (varText in context) {
            val variable = context.getSMVVariable(programRun, varText)
            if (isReference) {
                context.getReference(variable, Integer.parseInt(ctx.i().text))
            } else {
                variable
            }
        } else {
            if (isReference) {
                throw IllegalExpressionException(
                    "You referenced a variable $varText, " +
                        "but it is not found as a defined program variable.",
                )
            }
            SEnumLiteral(varText.uppercase(Locale.getDefault()))
        }
    }

    override fun visitLogicalAnd(ctx: TestTableLanguageParser.LogicalAndContext): SMVExpr =
        SBinaryExpression(ctx.left.accept(this), SBinaryOperator.AND, ctx.right.accept(this))

    override fun visitLogicalXor(ctx: TestTableLanguageParser.LogicalXorContext): SMVExpr =
        SBinaryExpression(ctx.left.accept(this), SBinaryOperator.XOR, ctx.right.accept(this))

    override fun visitBconstant(ctx: TestTableLanguageParser.BconstantContext): SMVExpr = ctx.constant().accept(this)

    override fun visitLogicalOr(ctx: TestTableLanguageParser.LogicalOrContext): SMVExpr =
        SBinaryExpression(ctx.left.accept(this), SBinaryOperator.OR, ctx.right.accept(this))

    override fun visitEquality(ctx: TestTableLanguageParser.EqualityContext): SMVExpr =
        SBinaryExpression(ctx.left.accept(this), SBinaryOperator.EQUAL, ctx.right.accept(this))

    override fun visitGuardedcommand(ctx: TestTableLanguageParser.GuardedcommandContext): SMVExpr {
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
        private val ENUM_TYPE = EnumType(LinkedList())
    }
}