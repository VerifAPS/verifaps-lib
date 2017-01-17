package edu.kit.iti.formal.stvs.model.expressions;

import java.util.List;

public class FunctionExpr extends Expression {

    public static enum Operation {
        AND,
        OR,
        EQUALS,
        GREATER_THAN,
        GREATER_EQUALS,
        LESS_THAN,
        LESS_EQUALS,
        NOT_EQUALS,
        PLUS,
        MINUS,
        MULTIPLICATION,
        DIVISION
    }

    private final Operation operation;
    private final List<Expression> arguments;

    public FunctionExpr(Operation op, List<Expression> arguments) {
        this.operation = op;
        this.arguments = arguments;
    }

    @Override
    public <R> R takeVisitor(ExpressionVisitor<R> visitor) {
        return visitor.visitFunctionExpr(this);
    }

    public Operation getOperation() {
        return operation;
    }

    public List<Expression> getArguments() {
        return arguments;
    }

    public boolean equals(FunctionExpr expr) {
        return getOperation().equals(expr.getOperation())
                && getArguments().equals(expr.getArguments());
    }

    @Override
    public boolean equals(Object other) {
        return (other instanceof FunctionExpr) && this.equals((FunctionExpr) other);
    }

    public String toString() {
        return "FunctionExpr(" + operation + ", " + arguments + ")";
    }

}
