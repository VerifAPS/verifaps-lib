package edu.kit.iti.formal.automation.testtables.io;

/*-
 * #%L
 * geteta
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

import edu.kit.iti.formal.automation.testtables.exception.IllegalExpressionException;
import edu.kit.iti.formal.automation.testtables.grammar.CellExpressionBaseVisitor;
import edu.kit.iti.formal.automation.testtables.grammar.CellExpressionParser;
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.smv.ast.*;

import javax.swing.plaf.SliderUI;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by weigl on 09.12.16.
 */
public class ExprVisitor extends CellExpressionBaseVisitor<SMVExpr> {
    private static final SMVType ENUM_TYPE = new SMVType.EnumType(new LinkedList<>());
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
            return constant.equal(columnVariable);
        }
        if (ctx.dontcare() != null)
            return ctx.dontcare().accept(this);
        if (ctx.interval() != null)
            return ctx.interval().accept(this);
        if (ctx.singlesided() != null)
            return ctx.singlesided().accept(this);
        if (ctx.expr() != null)
            return ctx.expr().accept(this);
        if (ctx.variable() != null) {
            SMVExpr v = ctx.variable().accept(this);
            return v.equal(columnVariable);
        }
        throw new IllegalStateException("No one of the N contexts matches");
    }

    @Override
    public SMVExpr visitDontcare(CellExpressionParser.DontcareContext ctx) {
        return SLiteral.TRUE;
    }

    @Override
    public SMVExpr visitConstantInt(CellExpressionParser.ConstantIntContext ctx) {
        return ctx.i().accept(this);
    }

    @Override
    public SMVExpr visitI(CellExpressionParser.IContext ctx) {
        return SLiteral.create(Long.parseLong(ctx.getText())).as(columnVariable.getSMVType());
    }

    @Override
    public SMVExpr visitConstantTrue(CellExpressionParser.ConstantTrueContext ctx) {
        return SLiteral.TRUE;
    }

    @Override
    public SMVExpr visitConstantFalse(CellExpressionParser.ConstantFalseContext ctx) {
        return SLiteral.FALSE;
    }


    @Override
    public SMVExpr visitSinglesided(CellExpressionParser.SinglesidedContext ctx) {
        String op = ctx.relational_operator().getStart().getText();
        SBinaryOperator relop = getsBinaryOperator(op);

        return columnVariable.op(relop, ctx.expr().accept(this));
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
        return ctx.variable().accept(this);
    }

    @Override
    public SMVExpr visitVariable(CellExpressionParser.VariableContext ctx) {
        SVariable var = gtt.getSMVVariable(ctx.IDENTIFIER().getText());
        boolean isReference = ctx.RBRACKET() != null;

        if (var == null) {
            if (isReference)
                throw new IllegalExpressionException(
                        "You referenced a variable " + ctx.IDENTIFIER().getText() + ", but it is not found as a defined io-variable.");
            return new SLiteral(ENUM_TYPE, ctx.IDENTIFIER().getText());
        }

        if (isReference)
            return gtt.getReference(var, Integer.parseInt(ctx.i().getText()));
        else
            return var;

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
