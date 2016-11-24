package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.LocalScope;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedinScope;
import edu.kit.iti.formal.automation.operators.BinaryOperator;
import edu.kit.iti.formal.automation.operators.Operators;
import edu.kit.iti.formal.automation.visitors.Visitor;

public class BinaryExpression extends Expression {
    private Expression leftExpr, rightExpr;
    private BinaryOperator operator;

    public BinaryExpression(Expression leftExpr, Expression rightExpr, BinaryOperator operator) {
        if (leftExpr == null || rightExpr == null || operator == null) {
            throw new IllegalArgumentException();
        }


        this.leftExpr = leftExpr;
        this.rightExpr = rightExpr;
        this.operator = operator;
    }

    public BinaryExpression(Expression leftExpr, Expression rightExpr, String operator) {
        this.leftExpr = leftExpr;
        this.rightExpr = rightExpr;
        this.operator = (BinaryOperator) Operators.lookup(operator);
    }


    public Expression getLeftExpr() {
        return leftExpr;
    }

    public void setLeftExpr(Expression leftExpr) {
        this.leftExpr = leftExpr;
    }

    public Expression getRightExpr() {
        return rightExpr;
    }

    public void setRightExpr(Expression rightExpr) {
        this.rightExpr = rightExpr;
    }

    public BinaryOperator getOperator() {
        return operator;
    }

    public void setOperator(BinaryOperator operator) {
        this.operator = operator;
    }

    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public Any dataType(LocalScope localScope) throws VariableNotDefinedinScope, TypeConformityException {
        Any a = leftExpr.dataType(localScope);
        Any b = rightExpr.dataType(localScope);
        Any c = operator.getPromotedType(a, b);
        if (c == null) throw new TypeConformityException(
                this, operator.getExpectedDataTypes(), a, b
        );
        return c;
    }


    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof BinaryExpression)) return false;

        BinaryExpression that = (BinaryExpression) o;

        if (!leftExpr.equals(that.leftExpr)) return false;
        if (operator != that.operator) return false;
        if (!rightExpr.equals(that.rightExpr)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        int result = leftExpr.hashCode();
        result = 31 * result + rightExpr.hashCode();
        result = 31 * result + operator.hashCode();
        return result;
    }
}
