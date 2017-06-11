package edu.kit.iti.formal.automation.st.ast;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.automation.operators.BinaryOperator;
import edu.kit.iti.formal.automation.operators.Operators;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * <p>BinaryExpression class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class BinaryExpression extends Expression {
    private Expression leftExpr, rightExpr;
    private BinaryOperator operator;

    /**
     * <p>Constructor for BinaryExpression.</p>
     *
     * @param leftExpr a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     * @param rightExpr a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     * @param operator a {@link edu.kit.iti.formal.automation.operators.BinaryOperator} object.
     */
    public BinaryExpression(Expression leftExpr, Expression rightExpr, BinaryOperator operator) {
        if (leftExpr == null || rightExpr == null || operator == null) {
            throw new IllegalArgumentException();
        }


        this.leftExpr = leftExpr;
        this.rightExpr = rightExpr;
        this.operator = operator;
    }

    /**
     * <p>Constructor for BinaryExpression.</p>
     *
     * @param leftExpr a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     * @param rightExpr a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     * @param operator a {@link java.lang.String} object.
     */
    public BinaryExpression(Expression leftExpr, Expression rightExpr, String operator) {
        this.leftExpr = leftExpr;
        this.rightExpr = rightExpr;
        this.operator = (BinaryOperator) Operators.lookup(operator);
    }


    /**
     * <p>Getter for the field <code>leftExpr</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public Expression getLeftExpr() {
        return leftExpr;
    }

    /**
     * <p>Setter for the field <code>leftExpr</code>.</p>
     *
     * @param leftExpr a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public void setLeftExpr(Expression leftExpr) {
        this.leftExpr = leftExpr;
    }

    /**
     * <p>Getter for the field <code>rightExpr</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public Expression getRightExpr() {
        return rightExpr;
    }

    /**
     * <p>Setter for the field <code>rightExpr</code>.</p>
     *
     * @param rightExpr a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public void setRightExpr(Expression rightExpr) {
        this.rightExpr = rightExpr;
    }

    /**
     * <p>Getter for the field <code>operator</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.operators.BinaryOperator} object.
     */
    public BinaryOperator getOperator() {
        return operator;
    }

    /**
     * <p>Setter for the field <code>operator</code>.</p>
     *
     * @param operator a {@link edu.kit.iti.formal.automation.operators.BinaryOperator} object.
     */
    public void setOperator(BinaryOperator operator) {
        this.operator = operator;
    }

    /** {@inheritDoc} */
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /** {@inheritDoc} */
    @Override
    public Any dataType(LocalScope localScope) throws VariableNotDefinedException, TypeConformityException {
        Any a = leftExpr.dataType(localScope);
        Any b = rightExpr.dataType(localScope);
        Any c = operator.getPromotedType(a, b);
        if (c == null) throw new TypeConformityException(
                this, operator.getExpectedDataTypes(), a, b
        );
        return c;
    }

    @Override public BinaryExpression clone() {
        return new BinaryExpression(leftExpr.clone(), rightExpr.clone(),
                operator);
    }

    /** {@inheritDoc} */
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

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        int result = leftExpr.hashCode();
        result = 31 * result + rightExpr.hashCode();
        result = 31 * result + operator.hashCode();
        return result;
    }
}
