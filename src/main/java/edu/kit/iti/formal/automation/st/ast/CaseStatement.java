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
import java.util.stream.Collectors;

/**
 * Created by weigla on 09.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class CaseStatement extends Statement {
    private Expression expression;
    private List<Case> cases = new ArrayList<>();
    private StatementList elseCase = new StatementList();

    /** {@inheritDoc} */
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * <p>addCase.</p>
     *
     * @param cs a {@link edu.kit.iti.formal.automation.st.ast.CaseStatement.Case} object.
     */
    public void addCase(Case cs) {
        cases.add(cs);
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
     * <p>Getter for the field <code>cases</code>.</p>
     *
     * @return a {@link java.util.List} object.
     */
    public List<Case> getCases() {
        return cases;
    }

    /**
     * <p>Setter for the field <code>cases</code>.</p>
     *
     * @param cases a {@link java.util.List} object.
     */
    public void setCases(List<Case> cases) {
        this.cases = cases;
    }

    /**
     * <p>Getter for the field <code>elseCase</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public StatementList getElseCase() {
        return elseCase;
    }

    /**
     * <p>Setter for the field <code>elseCase</code>.</p>
     *
     * @param elseCase a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public void setElseCase(StatementList elseCase) {
        this.elseCase = elseCase;
    }

    @Override public CaseStatement clone() {
        CaseStatement c = new CaseStatement();
        cases.forEach(cs -> c.addCase(cs.clone()));
        return c;
    }

    public static class Case extends Top {
        List<CaseConditions> conditions = new ArrayList<>();
        StatementList statements = new StatementList();

        public void addCondition(CaseConditions condition) {
            conditions.add(condition);
        }

        public List<CaseConditions> getConditions() {
            return conditions;
        }

        public void setConditions(List<CaseConditions> conditions) {
            this.conditions = conditions;
        }

        public StatementList getStatements() {
            return statements;
        }

        public void setStatements(StatementList statements) {
            this.statements = statements;
        }

        @Override
        public <T> T visit(Visitor<T> visitor) {
            return visitor.visit(this);
        }

        @Override public Case clone() {
            Case c = new Case();
            c.conditions = conditions.stream().map(CaseConditions::clone)
                    .collect(Collectors.toList());
            c.statements = statements.clone();
            return c;
        }
    }
}
