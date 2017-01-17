package edu.kit.iti.formal.stvs.model.expressions;

public class VariableExpr extends Expression {

    private final String varName;

    public VariableExpr(String varName) {
        this.varName = varName;
    }

    @Override
    public <R> R takeVisitor(ExpressionVisitor<R> visitor) {
        return visitor.visitVariable(this);
    }

    public String getVariableName() {
        return varName;
    }

    public boolean equals(VariableExpr expr) {
        return getVariableName().equals(expr.getVariableName());
    }

    @Override
    public boolean equals(Object other) {
        return (other instanceof VariableExpr) && this.equals((VariableExpr) other);
    }

    public String toString() {
        return "VariableExpr(" + varName + ")";
    }

}
