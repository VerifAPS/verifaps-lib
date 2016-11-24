package edu.kit.iti.formal.automation.st.ast;


import edu.kit.iti.formal.automation.LocalScope;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedinScope;
import edu.kit.iti.formal.automation.operators.UnaryOperator;
import edu.kit.iti.formal.automation.visitors.Visitor;

public class UnaryExpression extends Expression {
    UnaryOperator operator;
    Expression expression;

    public UnaryExpression(UnaryOperator operator, Expression expression) {
        this.operator = operator;
        this.expression = expression;
    }

    public UnaryOperator getOperator() {
        return operator;
    }

    public void setOperator(UnaryOperator operator) {
        this.operator = operator;
    }

    public Expression getExpression() {
        return expression;
    }

    public void setExpression(Expression expression) {
        this.expression = expression;
    }

    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public Any dataType(LocalScope localScope) throws VariableNotDefinedinScope, TypeConformityException {
        Any a = operator.getPromotedType(expression.dataType(localScope));
        if (a == null) {
            throw new TypeConformityException(this, operator.getExpectedDataTypes(), a);
        }
        return a;
    }


    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof UnaryExpression)) return false;

        UnaryExpression that = (UnaryExpression) o;

        if (!expression.equals(that.expression)) return false;
        if (operator != that.operator) return false;

        return true;
    }

    @Override
    public int hashCode() {
        int result = operator.hashCode();
        result = 31 * result + expression.hashCode();
        return result;
    }
}
