package edu.kit.iti.formal.automation.st0.trans;

/*-
 * #%L
 * iec-symbex
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

import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstCopyVisitor;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

/**
 * Created by weigl on 03/10/14.
 * @author Alexander Weigl
 */
public class ExpressionReplacer extends AstCopyVisitor {
    private StatementList statements;
    private Map<Expression, Expression> replacements = new HashMap<>();

    public StatementList getStatements() {
        return statements;
    }

    public void setStatements(StatementList statements) {
        this.statements = statements;
    }

    public Map<Expression, Expression> getReplacements() {
        return replacements;
    }

    public void setReplacements(Map<Expression, Expression> replacements) {
        this.replacements = replacements;
    }


    @Override
    public Object visit(SymbolicReference symbolicReference) {
        if (replacements.containsKey(symbolicReference)) {
            return replacements.get(symbolicReference);
        }
        return super.visit(symbolicReference);
    }

    @Override
    public Object visit(UnaryExpression unaryExpression) {
        if (replacements.containsKey(unaryExpression)) {
            return replacements.get(unaryExpression);
        }
        return super.visit(unaryExpression);
    }

    @Override
    public Object visit(BinaryExpression binaryExpression) {
        if (replacements.containsKey(binaryExpression)) {
            return replacements.get(binaryExpression);
        }
        return super.visit(binaryExpression);
    }

    public Collection<? extends Statement> replace() {
        return (StatementList) getStatements().visit(this);
    }
}
