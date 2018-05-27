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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.st.ast.BinaryExpression;
import edu.kit.iti.formal.automation.st.ast.Expression;
import edu.kit.iti.formal.automation.st.ast.SymbolicReference;
import edu.kit.iti.formal.automation.st.ast.UnaryExpression;
import edu.kit.iti.formal.automation.st.util.AstVisitor;

import java.util.Map;

/**
 * @author Alexander Weigl (26.06.2014)
 * @version 1
 */
public class ExpressionEmbedder extends AstVisitor<Object> {
    private final Map<Expression, Expression> assignments;

    public ExpressionEmbedder(Map<Expression, Expression> assignments) {
        this.assignments = assignments;
    }

    @Override
    public Object visit(BinaryExpression binaryExpression) {
        return super.visit(binaryExpression);
    }

    @Override
    public Object visit(UnaryExpression unaryExpression) {
        return super.visit(unaryExpression);
    }

    @Override
    public Object visit(SymbolicReference symbolicReference) {
        return copyOrSubstitute(symbolicReference);
    }

    private Expression copyOrSubstitute(Expression expression) {
        return assignments.getOrDefault(expression,
                //TODO infinite loop call
                (Expression) expression.accept(this));
    }
}
