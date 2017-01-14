package edu.kit.iti.formal.stvs.model.expressions;

public class LiteralExpr extends Expression {

    private final Value value;

    public LiteralExpr(Value val) {
        this.value = val;
    }

    @Override
    public <R> R takeVisitor(ExpressionVisitor<R> visitor) {
        return visitor.visitLiteral(this);
    }

    public Value getValue() {
        return value;
    }

}
