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

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigla on 09.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class IfStatement extends Statement {
    private List<GuardedStatement> conditionalBranches = new ArrayList<>();
    private StatementList elseBranch = new StatementList();


    /**
     * <p>addGuardedCommand.</p>
     *
     * @param expr a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     * @param statements a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.GuardedStatement} object.
     */
    public GuardedStatement addGuardedCommand(Expression expr, StatementList statements) {
        if (expr == null)
            throw new IllegalArgumentException();

        GuardedStatement e = new GuardedStatement(expr, statements);
        conditionalBranches.add(e);
        return e;
    }

    /**
     * <p>Getter for the field <code>conditionalBranches</code>.</p>
     *
     * @return a {@link java.util.List} object.
     */
    public List<GuardedStatement> getConditionalBranches() {
        return conditionalBranches;
    }

    /**
     * <p>Setter for the field <code>conditionalBranches</code>.</p>
     *
     * @param conditionalBranches a {@link java.util.List} object.
     */
    public void setConditionalBranches(List<GuardedStatement> conditionalBranches) {
        this.conditionalBranches = conditionalBranches;
    }

    /**
     * <p>Getter for the field <code>elseBranch</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public StatementList getElseBranch() {
        return elseBranch;
    }

    /**
     * <p>Setter for the field <code>elseBranch</code>.</p>
     *
     * @param elseBranch a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public void setElseBranch(StatementList elseBranch) {
        this.elseBranch = elseBranch;
    }

    /** {@inheritDoc} */
    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * <p>addGuardedCommand.</p>
     *
     * @param gc a {@link edu.kit.iti.formal.automation.st.ast.GuardedStatement} object.
     */
    public void addGuardedCommand(GuardedStatement gc) {
        conditionalBranches.add(gc);
    }
}
