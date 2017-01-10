package edu.kit.iti.formal.stvs.model.expressions;

import java.util.List;

public class FunctionExpr extends Expression {

    public static enum Operation {
        AND,
        OR,
        EQUALS,
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

}
