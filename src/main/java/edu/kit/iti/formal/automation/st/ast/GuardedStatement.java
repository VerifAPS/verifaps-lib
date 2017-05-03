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
 * Created by weigla on 09.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class GuardedStatement extends Statement {
    protected Expression condition;
    protected StatementList statements = new StatementList();

    /**
     * <p>Constructor for GuardedStatement.</p>
     */
    public GuardedStatement() {

    }

    /**
     * <p>Constructor for GuardedStatement.</p>
     *
     * @param condition a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     * @param statements a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public GuardedStatement(Expression condition, StatementList statements) {
        this.condition = condition;
        this.statements = statements;
    }

    /**
     * <p>Getter for the field <code>condition</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public Expression getCondition() {
        return condition;
    }

    /**
     * <p>Setter for the field <code>condition</code>.</p>
     *
     * @param condition a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public void setCondition(Expression condition) {
        this.condition = condition;
    }


    /**
     * <p>Getter for the field <code>statements</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public StatementList getStatements() {
        return statements;
    }

    /**
     * <p>Setter for the field <code>statements</code>.</p>
     *
     * @param statements a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public void setStatements(StatementList statements) {
        this.statements = statements;
    }

    /** {@inheritDoc} */
    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override public GuardedStatement clone() {
        GuardedStatement gs = new GuardedStatement();
        gs.condition = condition.clone();
        gs.statements = statements.clone();
        return gs;
    }
}
