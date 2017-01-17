package edu.kit.iti.formal.stvs.model.expressions;

import java.util.Arrays;

/**
 * Created by philipp on 17.01.17.
 */
public final class SimpleExpressions {

    private SimpleExpressions() {
    }

    public static Expression and(Expression e1, Expression e2) {
        return new FunctionExpr(FunctionExpr.Operation.AND, Arrays.asList(e1, e2));
    }

    public static Expression plus(Expression e1, Expression e2) {
        return new FunctionExpr(FunctionExpr.Operation.PLUS, Arrays.asList(e1, e2));
    }

    public static Expression eq(Expression e1, Expression e2) {
        return new FunctionExpr(FunctionExpr.Operation.EQUALS, Arrays.asList(e1, e2));
    }

    public static Expression var(String name) {
        return new VariableExpr(name);
    }

    public static Expression literal(int integer) {
        return new LiteralExpr(new ValueInt(integer));
    }

    public static Expression literal(boolean bool) {
        return new LiteralExpr(ValueBool.of(bool));
    }

    public static Expression literal(ValueEnum e) {
        return new LiteralExpr(e);
    }

}
