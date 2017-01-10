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

}
