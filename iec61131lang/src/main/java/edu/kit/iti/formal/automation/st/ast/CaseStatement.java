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


import edu.kit.iti.formal.automation.visitors.Utils;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by weigla on 09.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
@Data
@EqualsAndHashCode(callSuper = false)
public class CaseStatement extends Statement {
    private Expression expression;
    private List<Case> cases = new ArrayList<>();
    private StatementList elseCase = new StatementList();

    /**
     * {@inheritDoc}
     */
    public <T> T accept(Visitor<T> visitor) {
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



    @Override
    public CaseStatement copy() {
        CaseStatement c = new CaseStatement();
        c.setRuleContext(getRuleContext());
        c.expression = expression.copy();
        cases.forEach(cs -> c.addCase(cs.copy()));
        c.elseCase = Utils.copyNull(getElseCase());
        return c;
    }

    @Data
    @EqualsAndHashCode
    @NoArgsConstructor
    @AllArgsConstructor
    public static class Case extends Top {
        List<CaseCondition> conditions = new ArrayList<>();
        StatementList statements = new StatementList();

        public void addCondition(CaseCondition condition) {
            conditions.add(condition);
        }

        public <T> T accept(Visitor<T> visitor) {
            return visitor.visit(this);
        }

        @Override
        public Case copy() {
            Case c = new Case();
            c.conditions = conditions.stream()
                    .map(CaseCondition::copy)
                    .collect(Collectors.toList());
            c.statements = statements.copy();
            return c;
        }
    }
}
