package edu.kit.iti.formal.automation.ast;


import edu.kit.iti.formal.automation.visitors.Visitor;

public class UnaryExpression extends Expression {
    Operator operator;
    Expression expression;

    public UnaryExpression(Operator operator, Expression expression) {
        this.operator = operator;
        this.expression = expression;
    }

    public Operator getOperator() {
        return operator;
    }

    public void setOperator(Operator operator) {
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


    public static enum Operator {
        MINUS("-"), NEGATE("NOT");

        public final String symbol;

        Operator(String symbol) {
            this.symbol = symbol;
        }
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
