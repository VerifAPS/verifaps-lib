package edu.kit.iti.formal.automation.testtables.io


import edu.kit.iti.formal.automation.testtables.exception.IllegalExpressionException
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageBaseVisitor
import edu.kit.iti.formal.automation.testtables.grammar.TestTableLanguageParser
import edu.kit.iti.formal.automation.testtables.model.ParseContext
import edu.kit.iti.formal.smv.EnumType
import edu.kit.iti.formal.smv.ast.*
import java.util.*

/**
 * Created by weigl on 09.12.16.
 */
class ExprVisitor(private val columnVariable: SVariable,
                  private val columnProgramRun: Int?,
                  private val context: ParseContext) : TestTableLanguageBaseVisitor<SMVExpr>() {

    override fun visitCell(ctx: TestTableLanguageParser.CellContext): SMVExpr {
        return ctx.chunk().map { this.visitChunk(it) }
                .reduce { a, b -> SBinaryExpression(a, SBinaryOperator.AND, b) }
    }

    override fun visitChunk(ctx: TestTableLanguageParser.ChunkContext): SMVExpr {
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

    override fun visitDontcare(ctx: TestTableLanguageParser.DontcareContext): SMVExpr {
        return SLiteral.TRUE
    }

    override fun visitConstantInt(ctx: TestTableLanguageParser.ConstantIntContext): SMVExpr {
        return ctx.i().accept(this)
    }

    override fun visitI(ctx: TestTableLanguageParser.IContext): SMVExpr {
        return SLiteral.create(java.lang.Long.parseLong(ctx.text)).with(columnVariable.dataType!!)
    }

    override fun visitConstantTrue(ctx: TestTableLanguageParser.ConstantTrueContext): SMVExpr {
        return SLiteral.TRUE
    }

    override fun visitConstantFalse(ctx: TestTableLanguageParser.ConstantFalseContext): SMVExpr {
        return SLiteral.FALSE
    }


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
                SBinaryExpression(columnVariable, SBinaryOperator.LESS_EQUAL, b))
    }

    override fun visitMinus(ctx: TestTableLanguageParser.MinusContext): SMVExpr {
        return SUnaryExpression(SUnaryOperator.MINUS, ctx.expr().accept(this))
    }


    override fun visitNegation(ctx: TestTableLanguageParser.NegationContext): SMVExpr {
        return SUnaryExpression(SUnaryOperator.NEGATE, ctx.expr().accept(this))
    }

    override fun visitParens(ctx: TestTableLanguageParser.ParensContext): SMVExpr {
        return ctx.expr().accept(this)
    }

    override fun visitCompare(ctx: TestTableLanguageParser.CompareContext): SMVExpr {
        val op = getsBinaryOperator(ctx.op.text)
        return SBinaryExpression(ctx.left.accept(this),
                op, ctx.right.accept(this))
    }

    override fun visitMod(ctx: TestTableLanguageParser.ModContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.MOD, ctx.right.accept(this))
    }

    override fun visitPlus(ctx: TestTableLanguageParser.PlusContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.PLUS, ctx.right.accept(this))
    }

    override fun visitDiv(ctx: TestTableLanguageParser.DivContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.DIV, ctx.right.accept(this))
    }

    override fun visitInequality(ctx: TestTableLanguageParser.InequalityContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.NOT_EQUAL, ctx.right.accept(this))
    }

    override fun visitSubstract(ctx: TestTableLanguageParser.SubstractContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.MINUS, ctx.right.accept(this))
    }

    override fun visitMult(ctx: TestTableLanguageParser.MultContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.MUL, ctx.right.accept(this))
    }

    override fun visitBinguardedCommand(ctx: TestTableLanguageParser.BinguardedCommandContext): SMVExpr {
        return ctx.guardedcommand().accept(this)
    }

    override fun visitFunctioncall(ctx: TestTableLanguageParser.FunctioncallContext): SMVExpr {
        //TODO call function/symbolic execution
        val args = ctx.expr().map { c -> c.accept(this) }
        return SFunction(ctx.IDENTIFIER().text,
                *args.toTypedArray())
    }

    override fun visitBvariable(ctx: TestTableLanguageParser.BvariableContext): SMVExpr {
        return ctx.variable().accept(this)
    }

    override fun visitVariable(ctx: TestTableLanguageParser.VariableContext): SMVExpr {
        val programRun = when {
            ctx.RV_SEPARATOR() == null -> columnProgramRun
            ctx.INTEGER() != null -> ctx.INTEGER().text.toInt()
            else -> columnProgramRun?.let { 1 - it } // other run
        }

        val varText =
                if (ctx.RV_SEPARATOR() != null && ctx.IDENTIFIER() == null)
                    columnVariable.name
                else
                    ctx.IDENTIFIER().text

        val isReference = ctx.RBRACKET() != null

        return if ( varText in context) {
            val variable = context.getSMVVariable(programRun, varText)
            if (isReference)
                context.getReference(variable, Integer.parseInt(ctx.i().text))
            else
                variable
        } else {
            if (isReference)
                throw IllegalExpressionException("You referenced a variable $varText, " +
                        "but it is not found as a defined program variable.")
            SLiteral(varText, ENUM_TYPE)
        }
    }

    override fun visitLogicalAnd(ctx: TestTableLanguageParser.LogicalAndContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.AND, ctx.right.accept(this))
    }

    override fun visitLogicalXor(ctx: TestTableLanguageParser.LogicalXorContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.XOR, ctx.right.accept(this))
    }

    override fun visitBconstant(ctx: TestTableLanguageParser.BconstantContext): SMVExpr {
        return ctx.constant().accept(this)
    }

    override fun visitLogicalOr(ctx: TestTableLanguageParser.LogicalOrContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.OR, ctx.right.accept(this))
    }

    override fun visitEquality(ctx: TestTableLanguageParser.EqualityContext): SMVExpr {
        return SBinaryExpression(ctx.left.accept(this), SBinaryOperator.EQUAL, ctx.right.accept(this))
    }

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
