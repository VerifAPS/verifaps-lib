package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.HashMap;
import java.util.Map;

public class BinaryExpression extends Expression {
    public static final Map<String, Operator> OPERATOR_MAP = new HashMap<>();

    static {
        for (Operator o : Operator.values()) {
            OPERATOR_MAP.put(o.symbol, o);
        }
    }

    private Expression leftExpr, rightExpr;
    private Operator operator;

    public BinaryExpression(Expression leftExpr, Expression rightExpr, Operator operator) {
        if (leftExpr == null || rightExpr == null || operator == null) {
            throw new IllegalArgumentException();
        }


        this.leftExpr = leftExpr;
        this.rightExpr = rightExpr;
        this.operator = operator;
    }

    public BinaryExpression(Expression leftExpr, Expression rightExpr, String operator) {
        this(leftExpr, rightExpr, OPERATOR_MAP.get(operator));
    }


    public static Map<String, Operator> getOperatorMap() {
        return OPERATOR_MAP;
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

    public Operator getOperator() {
        return operator;
    }

    public void setOperator(Operator operator) {
        this.operator = operator;
    }

    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    public static enum Operator {
        //airthmetic
        ADD("+"),
        MULT("*"),
        SUB("-"),
        DIV("/"),
        MOD("MOD"),

        //logical
        AND("AND"),
        OR("OR"),
        XOR("XOR"),

        //comparison
        EQUALS("="),
        NOT_EQUALS("<>"),

        POWER("**"),

        LESS_THAN("<"),
        GREATER_THAN(">"),
        GREATER_EQUALS(">="),
        LESS_EQUALS("<=");

        public final String symbol;

        Operator(String t) {
            symbol = t;
        }
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
