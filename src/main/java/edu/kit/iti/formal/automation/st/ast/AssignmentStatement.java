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

import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 11.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class AssignmentStatement extends Statement {
    private Reference variable;
    private Expression expression;

    /**
     * <p>Constructor for AssignmentStatement.</p>
     */
    public AssignmentStatement() {
    }

    /**
     * <p>Constructor for AssignmentStatement.</p>
     *
     * @param variable a {@link edu.kit.iti.formal.automation.st.ast.Reference} object.
     * @param expression a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public AssignmentStatement(Reference variable, Expression expression) {
        this.variable = variable;
        this.expression = expression;
    }


    /** {@inheritDoc} */
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * <p>getLocation.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.Reference} object.
     */
    public Reference getLocation() {
        return variable;
    }

    /**
     * <p>setLocation.</p>
     *
     * @param variable a {@link edu.kit.iti.formal.automation.st.ast.Reference} object.
     */
    public void setLocation(Reference variable) {
        this.variable = variable;
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
}
