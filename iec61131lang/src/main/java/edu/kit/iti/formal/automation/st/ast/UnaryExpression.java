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
import edu.kit.iti.formal.automation.operators.UnaryOperator;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.ToString;

/**
 * <p>UnaryExpression class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
@Data
@EqualsAndHashCode
@ToString
public class UnaryExpression extends Expression {
    UnaryOperator operator;
    Expression expression;

    /**
     * <p>Constructor for UnaryExpression.</p>
     *
     * @param operator   a {@link edu.kit.iti.formal.automation.operators.UnaryOperator} object.
     * @param expression a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public UnaryExpression(UnaryOperator operator, Expression expression) {
        this.operator = operator;
        this.expression = expression;
    }

    /**
     * <p>Getter for the field <code>operator</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.operators.UnaryOperator} object.
     */
    public UnaryOperator getOperator() {
        return operator;
    }

    /**
     * <p>Setter for the field <code>operator</code>.</p>
     *
     * @param operator a {@link edu.kit.iti.formal.automation.operators.UnaryOperator} object.
     */
    public void setOperator(UnaryOperator operator) {
        this.operator = operator;
    }

    /**
     * <p>Getter for the field <code>expression</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public Expression getExpression() {
        return expression;
    }

    /**
     * <p>Setter for the field <code>expression</code>.</p>
     *
     * @param expression a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public void setExpression(Expression expression) {
        this.expression = expression;
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
        Any a = operator.getPromotedType(expression.dataType(localScope));
        if (a == null) {
            throw new TypeConformityException(this, operator.getExpectedDataTypes(), a);
        }
        return a;
    }

    @Override
    public UnaryExpression copy() {
        UnaryExpression ue = new UnaryExpression(operator, expression.copy());
        ue.setRuleContext(getRuleContext());
        return ue;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof UnaryExpression)) return false;

        UnaryExpression that = (UnaryExpression) o;

        if (!expression.equals(that.expression)) return false;
        if (operator != that.operator) return false;

        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        int result = operator.hashCode();
        result = 31 * result + expression.hashCode();
        return result;
    }
}
