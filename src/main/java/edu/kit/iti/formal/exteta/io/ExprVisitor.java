package edu.kit.iti.formal.exteta.io;

import edu.kit.iti.formal.exteta.grammar.CellExpressionBaseVisitor;
import edu.kit.iti.formal.exteta.grammar.CellExpressionParser;
import edu.kit.iti.formal.exteta.model.GeneralizedTestTable;
import edu.kit.iti.formal.exteta.schema.IoVariable;
import edu.kit.iti.formal.smv.BExpressionBuilder;
import edu.kit.iti.formal.smv.ast.*;
import org.antlr.v4.runtime.atn.SemanticContext;
import org.antlr.v4.runtime.tree.ParseTree;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Created by weigl on 09.12.16.
 */
public class ExprVisitor extends CellExpressionBaseVisitor<SMVExpr> {
    private final SVariable columnVariable;
    private final GeneralizedTestTable gtt;

    public ExprVisitor(SVariable column, GeneralizedTestTable vars) {
        columnVariable = column;
        gtt = vars;
    }

    @Override
    public SMVExpr visitCell(CellExpressionParser.CellContext ctx) {
        return ctx.chunk().stream()
                .map(this::visitChunk)
                .reduce((a, b) -> new SBinaryExpression(a, SBinaryOperator.AND, b))
                .get();
    }

    @Override
    public SMVExpr visitChunk(CellExpressionParser.ChunkContext ctx) {
        if (ctx.constant() != null) {
            SMVExpr constant = ctx.constant().accept(this);
            return BExpressionBuilder.expr(constant).equal().to(columnVariable).get();
        }
        if (ctx.dontcare() != null)
            return ctx.dontcare().accept(this);
        if (ctx.interval() != null)
            return ctx.interval().accept(this);
        if (ctx.singlesided() != null)
            return ctx.singlesided().accept(this);
        if (ctx.expr() != null)
            return ctx.expr().accept(this);
        throw new IllegalStateException("No one of the four contexts matches");
    }

    @Override
    public SMVExpr visitDontcare(CellExpressionParser.DontcareContext ctx) {
        return SLiteral.TRUE;
    }

    @Override
    public SMVExpr visitConstant(CellExpressionParser.ConstantContext ctx) {
        SLiteral constant;
        if (ctx.IDENTIFIER() != null) {
            return gtt.getSMVVariable(ctx.IDENTIFIER().getText());
        } else if (ctx.INTEGER() != null) {
            constant = new SLiteral(columnVariable.getSMVType(),
                    Long.parseLong(ctx.INTEGER().getText()));
        } else {
            constant = new SLiteral(columnVariable.getSMVType(),
                    Boolean.parseBoolean(ctx.a.getText().toLowerCase()));
        }
        return constant;
    }


    @Override
    public SMVExpr visitSinglesided(CellExpressionParser.SinglesidedContext ctx) {
        String op = ctx.relational_operator().getStart().getText();
        SBinaryOperator relop = getsBinaryOperator(op);

        return BExpressionBuilder.expr(columnVariable).op(relop).to(
                ctx.expr().accept(this)).get();
    }

    private SBinaryOperator getsBinaryOperator(String op) {
        switch (op) {
            case "<=":
                return SBinaryOperator.LESS_EQUAL;
            case ">=":
                return SBinaryOperator.GREATER_EQUAL;
            case "<":
                return SBinaryOperator.LESS_THAN;

            case "=":
                return SBinaryOperator.EQUAL;
            case ">":
                return SBinaryOperator.GREATER_THAN;
            case "<>":
            case "!=":
                return SBinaryOperator.NOT_EQUAL;
        }
        return null;
    }

    @Override
    public SMVExpr visitInterval(CellExpressionParser.IntervalContext ctx) {
        SMVExpr a = ctx.lower.accept(this);
        SMVExpr b = ctx.upper.accept(this);

        return new SBinaryExpression(
                new SBinaryExpression(a, SBinaryOperator.LESS_EQUAL, columnVariable),
                SBinaryOperator.AND,
                new SBinaryExpression(columnVariable, SBinaryOperator.LESS_EQUAL, b));
    }

    @Override
    public SMVExpr visitMinus(CellExpressionParser.MinusContext ctx) {
        return new SUnaryExpression(SUnaryOperator.MINUS, ctx.expr().accept(this));
    }


    @Override
    public SMVExpr visitNegation(CellExpressionParser.NegationContext ctx) {
        return new SUnaryExpression(SUnaryOperator.NEGATE, ctx.expr().accept(this));
    }

    @Override
    public SMVExpr visitParens(CellExpressionParser.ParensContext ctx) {
        return ctx.expr().accept(this);
    }

    @Override
    public SMVExpr visitCompare(CellExpressionParser.CompareContext ctx) {
        SBinaryOperator op = getsBinaryOperator(ctx.op.getText());
        return new SBinaryExpression(ctx.left.accept(this),
                op, ctx.right.accept(this));
    }

    @Override
    public SMVExpr visitMod(CellExpressionParser.ModContext ctx) {
        return new SBinaryExpression(ctx.left.accept(this), SBinaryOperator.MOD, ctx.right.accept(this));
    }

    @Override
    public SMVExpr visitPlus(CellExpressionParser.PlusContext ctx) {
        return new SBinaryExpression(ctx.left.accept(this), SBinaryOperator.PLUS, ctx.right.accept(this));
    }

    @Override
    public SMVExpr visitDiv(CellExpressionParser.DivContext ctx) {
        return new SBinaryExpression(ctx.left.accept(this), SBinaryOperator.DIV, ctx.right.accept(this));
    }

    @Override
    public SMVExpr visitInequality(CellExpressionParser.InequalityContext ctx) {
        return new SBinaryExpression(ctx.left.accept(this), SBinaryOperator.NOT_EQUAL, ctx.right.accept(this));
    }

    @Override
    public SMVExpr visitSubstract(CellExpressionParser.SubstractContext ctx) {
        return new SBinaryExpression(ctx.left.accept(this), SBinaryOperator.MINUS, ctx.right.accept(this));
    }

    @Override
    public SMVExpr visitMult(CellExpressionParser.MultContext ctx) {
        return new SBinaryExpression(ctx.left.accept(this), SBinaryOperator.MUL, ctx.right.accept(this));
    }

    @Override
    public SMVExpr visitBinguardedCommand(CellExpressionParser.BinguardedCommandContext ctx) {
        return ctx.guardedcommand().accept(this);
    }

    @Override
    public SMVExpr visitFunctioncall(CellExpressionParser.FunctioncallContext ctx) {
        //TODO call function/symbolic execution
        List<SMVExpr> args = ctx.expr().stream().map((c) -> c.accept(this)).collect(Collectors.toList());
        return new SFunction(ctx.IDENTIFIER().getText(),
                args.toArray(new SMVExpr[args.size()]));
    }

    @Override
    public SMVExpr visitBvariable(CellExpressionParser.BvariableContext ctx) {
        return gtt.getSMVVariable(ctx.IDENTIFIER().getText());
    }

    @Override
    public SMVExpr visitLogicalAnd(CellExpressionParser.LogicalAndContext ctx) {
        return new SBinaryExpression(ctx.left.accept(this), SBinaryOperator.AND, ctx.right.accept(this));
    }

    @Override
    public SMVExpr visitLogicalXor(CellExpressionParser.LogicalXorContext ctx) {
        return new SBinaryExpression(ctx.left.accept(this), SBinaryOperator.XOR, ctx.right.accept(this));
    }

    @Override
    public SMVExpr visitBconstant(CellExpressionParser.BconstantContext ctx) {
        return ctx.constant().accept(this);
    }

    @Override
    public SMVExpr visitLogicalOr(CellExpressionParser.LogicalOrContext ctx) {
        return new SBinaryExpression(ctx.left.accept(this), SBinaryOperator.OR, ctx.right.accept(this));
    }

    @Override
    public SMVExpr visitEquality(CellExpressionParser.EqualityContext ctx) {
        return new SBinaryExpression(ctx.left.accept(this), SBinaryOperator.EQUAL, ctx.right.accept(this));
    }

    @Override
    public SMVExpr visitGuardedcommand(CellExpressionParser.GuardedcommandContext ctx) {
        SCaseExpression c = new SCaseExpression();
        try {
            for (int i = 0; true; i += 2) {
                SMVExpr g = ctx.expr(i).accept(this);
                SMVExpr t = ctx.expr(i + 1).accept(this);
                c.addCase(g, t);
            }
        } catch (NullPointerException npe) {
        }

        return c;
    }
}
