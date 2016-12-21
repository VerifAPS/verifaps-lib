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
public class ForStatement extends Statement {
    private String variable;
    private Expression start, stop, step;
    private StatementList statements = new StatementList();

    /**
     * <p>Constructor for ForStatement.</p>
     */
    public ForStatement() {
    }

    /**
     * <p>Constructor for ForStatement.</p>
     *
     * @param variable a {@link java.lang.String} object.
     * @param start a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     * @param stop a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     * @param step a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     * @param statements a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public ForStatement(String variable, Expression start, Expression stop, Expression step, StatementList statements) {
        this.variable = variable;
        this.start = start;
        this.stop = stop;
        this.step = step;
        this.statements = statements;
    }

    /**
     * <p>Getter for the field <code>variable</code>.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getVariable() {
        return variable;
    }

    /**
     * <p>Setter for the field <code>variable</code>.</p>
     *
     * @param variable a {@link java.lang.String} object.
     */
    public void setVariable(String variable) {
        this.variable = variable;
    }

    /**
     * <p>Getter for the field <code>start</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public Expression getStart() {
        return start;
    }

    /**
     * <p>Setter for the field <code>start</code>.</p>
     *
     * @param start a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public void setStart(Expression start) {
        this.start = start;
    }

    /**
     * <p>Getter for the field <code>stop</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public Expression getStop() {
        return stop;
    }

    /**
     * <p>Setter for the field <code>stop</code>.</p>
     *
     * @param stop a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public void setStop(Expression stop) {
        this.stop = stop;
    }

    /**
     * <p>Getter for the field <code>step</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public Expression getStep() {
        return step;
    }

    /**
     * <p>Setter for the field <code>step</code>.</p>
     *
     * @param step a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public void setStep(Expression step) {
        this.step = step;
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
}
