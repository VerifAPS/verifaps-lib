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
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.ToString;

/**
 * <p>BinaryExpression class.</p>
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
@EqualsAndHashCode(callSuper = false)
@ToString
@Data
public class BinaryExpression extends Expression {
    private Expression leftExpr, rightExpr;
    private BinaryOperator operator;

    public static BinaryExpression andExpression(Expression leftExpr, Expression rightExpr) {
        return new BinaryExpression(leftExpr, rightExpr, Operators.AND);
    }

    public static BinaryExpression equalsExpression(Expression leftExpr, Expression rightExpr) {
        return new BinaryExpression(leftExpr, rightExpr, Operators.EQUALS);
    }

    public static BinaryExpression greaterEqualsExpression(Expression leftExpr, Expression rightExpr) {
        return new BinaryExpression(leftExpr, rightExpr, Operators.GREATER_EQUALS);
    }

    public static BinaryExpression lessEqualsExpression(Expression leftExpr, Expression rightExpr) {
        return new BinaryExpression(leftExpr, rightExpr, Operators.LESS_EQUALS);
    }

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

    /**
     * {@inheritDoc}
     */
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
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

    @Override
    public BinaryExpression copy() {
        BinaryExpression be = new BinaryExpression(leftExpr.copy(),
                rightExpr.copy(),
                operator);
        be.setRuleContext(getRuleContext());
        return be;
    }
}
