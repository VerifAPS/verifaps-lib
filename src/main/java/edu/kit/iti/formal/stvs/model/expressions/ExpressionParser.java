package edu.kit.iti.formal.stvs.model.expressions;

import edu.kit.iti.formal.stvs.model.expressions.parser.CellExpressionBaseVisitor;
import edu.kit.iti.formal.stvs.model.expressions.parser.CellExpressionLexer;
import edu.kit.iti.formal.stvs.model.expressions.parser.CellExpressionParser;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.ParseTree;

import java.util.Arrays;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Created by philipp on 09.01.17.
 */
public class ExpressionParser extends CellExpressionBaseVisitor<Expression> {

    private Set<Type> typeContext;
    private Map<String, Type> variableContext;
    private String cellName;

    private Expression cellAsVariable;

    public ExpressionParser(String cellName, Set<Type> typeContext, Map<String, Type> variableContext) {
        this.typeContext = typeContext;
        this.variableContext = variableContext;
        this.cellName = cellName;

        this.cellAsVariable = new VariableExpr(cellName);
    }

    public Expression parseExpression(String expressionAsString) throws RecognitionException {
        CharStream charStream = new ANTLRInputStream(expressionAsString);
        CellExpressionLexer lexer = new CellExpressionLexer(charStream);
        TokenStream tokens = new CommonTokenStream(lexer);
        CellExpressionParser parser = new CellExpressionParser(tokens);
        return this.visit(parser.cell());
    }

    public Set<Type> getTypeContext() {
        return typeContext;
    }

    public void setTypeContext(Set<Type> typeContext) {
        this.typeContext = typeContext;
    }

    public Map<String, Type> getVariableContext() {
        return variableContext;
    }

    public void setVariableContext(Map<String, Type> variableContext) {
        this.variableContext = variableContext;
    }

    public String getCellName() {
        return cellName;
    }

    public void setCellName(String cellName) {
        this.cellName = cellName;
    }

    @Override
    public Expression visit(ParseTree tree) {
        return tree.accept(this);
    }

    @Override
    public Expression visitCell(CellExpressionParser.CellContext ctx) {
        Optional<Expression> optionalExpression = ctx.chunk().stream()
                .map(chunkContext -> chunkContext.accept(this))
                .reduce((e1, e2) ->
                        new FunctionExpr(FunctionExpr.Operation.AND, Arrays.asList(e1, e2)));
        return optionalExpression.get();
    }

    @Override
    public Expression visitDontcare(CellExpressionParser.DontcareContext ctx) {
        return new LiteralExpr(ValueBool.TRUE);
    }

    @Override
    public Expression visitConstant(CellExpressionParser.ConstantContext ctx) {
        Expression literalExpr = new LiteralExpr(valueFromConstantToken(ctx));
        System.out.println(ctx.depth());
        return new FunctionExpr(FunctionExpr.Operation.EQUALS,
                Arrays.asList(cellAsVariable, literalExpr));
    }

    private Value valueFromConstantToken(CellExpressionParser.ConstantContext ctx) {
        // I have to trust ANTLR to not have any other values here... :/
        switch (ctx.a.getType()) {
            case CellExpressionLexer.INTEGER: return new ValueInt(Integer.parseInt(ctx.getText()));
            case CellExpressionLexer.T: return ValueBool.TRUE;
            case CellExpressionLexer.F: return ValueBool.FALSE;
            default: return null;
        }
    }

    @Override
    public Expression visitSinglesided(CellExpressionParser.SinglesidedContext ctx) {
        FunctionExpr.Operation op = operationFromRelOpToken(ctx);
        Expression rightSide = ctx.expr().accept(this);
        return new FunctionExpr(op,
                Arrays.asList(cellAsVariable, rightSide));
    }

    private FunctionExpr.Operation operationFromRelOpToken(CellExpressionParser.SinglesidedContext ctx) {
        switch (ctx.op.relOp.getType()) {
            case CellExpressionLexer.EQUALS: return FunctionExpr.Operation.EQUALS;
            case CellExpressionLexer.NOT_EQUALS: return FunctionExpr.Operation.NOT_EQUALS;
            case CellExpressionLexer.GREATER_THAN: return FunctionExpr.Operation.GREATER_THAN;
            case CellExpressionLexer.GREATER_EQUALS: return FunctionExpr.Operation.GREATER_EQUALS;
            case CellExpressionLexer.LESS_THAN: return FunctionExpr.Operation.LESS_THAN;
            case CellExpressionLexer.LESS_EQUALS: return FunctionExpr.Operation.LESS_EQUALS;
            default: return null;
        }
    }

    @Override
    public Expression visitPlus(CellExpressionParser.PlusContext ctx) {
        Expression left = ctx.left.accept(this);
        Expression right = ctx.right.accept(this);
        return new FunctionExpr(FunctionExpr.Operation.PLUS,
                Arrays.asList(left, right));
    }

    @Override
    public Expression visitBconstant(CellExpressionParser.BconstantContext ctx) {
        return new LiteralExpr(valueFromConstantToken(ctx.constant()));
    }
}
