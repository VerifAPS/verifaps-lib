package edu.kit.iti.formal.automation.st0;

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2017 - 2018 Alexander Weigl
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

import edu.kit.iti.formal.automation.datatypes.AnyBit;
import edu.kit.iti.formal.automation.operators.Operators;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor;
import edu.kit.iti.formal.automation.st0.trans.ST0Transformation;
import sun.reflect.generics.reflectiveObjects.NotImplementedException;

public class TrivialBranchReducer implements ST0Transformation {
    @Override
    public void transform(STSimplifier.State state) {
        state.functions.values().parallelStream().forEach(this::process);
        process(state.theProgram);
    }

    private void process(TopLevelScopeElement topLevelScopeElement) {
        topLevelScopeElement.accept(new TrivialBranchReducerVisitor());
    }

    private class TrivialBranchReducerVisitor extends AstMutableVisitor {
        @Override
        public Object visit(IfStatement ifStatement) {
            IfStatement newIfStatement = new IfStatement();
            for (GuardedStatement guardedStatement : ifStatement.getConditionalBranches()) {
                guardedStatement.setStatements((StatementList) guardedStatement.getStatements().accept(this));
                boolean value = false;
                if (guardedStatement.getCondition() instanceof Literal)
                    value = evaluateTrivialCondition((Literal) guardedStatement.getCondition());
                else if (guardedStatement.getCondition() instanceof BinaryExpression
                        && ((BinaryExpression) guardedStatement.getCondition()).getLeftExpr() instanceof Literal
                        && ((BinaryExpression) guardedStatement.getCondition()).getRightExpr() instanceof Literal)
                    value = evaluateTrivialCondition((BinaryExpression) guardedStatement.getCondition());
                else  // non-trivial statement
                    newIfStatement.addGuardedCommand(guardedStatement);
                // Handle trivial guard
                if (value && newIfStatement.getConditionalBranches().size() == 0)
                    return guardedStatement.getStatements().accept(this);
                else if (value) {
                    newIfStatement.setElseBranch(guardedStatement.getStatements());
                    return newIfStatement;
                }
                // else continue
            }
            newIfStatement.setElseBranch((StatementList) ifStatement.getElseBranch().accept(this));
            return newIfStatement;
        }

        private boolean evaluateTrivialCondition(Literal literal) {
            if (!literal.getDataType().equals(AnyBit.BOOL))
                throw new IllegalArgumentException();
            return literal.getTextValue().equals("TRUE");
        }

        private boolean evaluateTrivialCondition(BinaryExpression binaryExpression) {
            if (!(binaryExpression.getLeftExpr() instanceof Literal)
                    || !(binaryExpression.getRightExpr() instanceof Literal))
                throw new IllegalArgumentException();
            int left = Integer.valueOf(((Literal) binaryExpression.getLeftExpr()).getText());
            int right = Integer.valueOf(((Literal) binaryExpression.getRightExpr()).getText());
            if (!binaryExpression.getOperator().equals(Operators.EQUALS))
                throw new NotImplementedException();
            return left == right;
        }
    }
}
