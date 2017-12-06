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

import edu.kit.iti.formal.automation.datatypes.DataTypes;
import edu.kit.iti.formal.automation.datatypes.RangeType;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import edu.kit.iti.formal.automation.st0.STSimplifier;
import edu.kit.iti.formal.automation.visitors.Visitable;
import lombok.AllArgsConstructor;
import lombok.Getter;

import java.util.stream.Collectors;

/**
 * Created by weigl on 03/10/14.
 * @author Alexander Weigl, Augusto Modanese
 */
public class ArrayEmbedder implements ST0Transformation {
    private STSimplifier.State state;

    @Override
    public void transform(STSimplifier.State state) {
        this.state = state;
        for (VariableDeclaration arrayVariable : state.theProgram.getLocalScope().stream()
                .filter(v -> v.getTypeDeclaration() instanceof ArrayTypeDeclaration)
                .collect(Collectors.toList())) {
            ArrayTypeDeclaration array = (ArrayTypeDeclaration) arrayVariable.getTypeDeclaration();
            assert array.getInitialization() != null;
            for (Range range : array.getRanges()) {
                int rangeMin = Integer.parseInt(range.getStart().getText());
                int rangeMax = Integer.parseInt(range.getStop().getText());
                // TODO multiple ranges
                for (int i = rangeMin; i <= rangeMax; i++) {
                    VariableDeclaration var = new VariableDeclaration(arrayVariable.getIdentifier() + "$" + i,
                            new SimpleTypeDeclaration(array.getBaseType(),
                                    array.getInitialization().get(i - rangeMin)));
                    if (arrayVariable.isGlobal())
                        var.setType(VariableDeclaration.GLOBAL);
                    state.theProgram.getLocalScope().add(var);
                }
            }
            ArrayEmbedderVisitor arrayEmbedderVisitor = new ArrayEmbedderVisitor(arrayVariable);
            state.functions.values().forEach(f -> f.accept(arrayEmbedderVisitor));
            state.theProgram.accept(arrayEmbedderVisitor);
            state.theProgram.getLocalScope().getLocalVariables().remove(arrayVariable.getName());
        }
    }

    @Getter
    @AllArgsConstructor
    private static class ArrayAccessRenameVisitor extends AstMutableVisitor {
        private final String toRename;
        private final int access;

        @Override
        public Object visit(SymbolicReference symbolicReference) {
            if (symbolicReference.getIdentifier().equals(toRename) && symbolicReference.hasSubscripts()) {
                symbolicReference.setIdentifier(toRename + "$" + access);
                symbolicReference.setSubscripts(null);
            }
            return super.visit(symbolicReference);
        }
    }

    @Getter
    @AllArgsConstructor
    private class ArrayEmbedderVisitor extends AstMutableVisitor {
        private final VariableDeclaration arrayVariable;

        Object visit(Statement statement) {
            FindReferenceWithSubscriptVisitor findReferenceWithSubscriptVisitor = new FindReferenceWithSubscriptVisitor();
            statement.accept(findReferenceWithSubscriptVisitor);
            IfStatement branch = new IfStatement();
            while (findReferenceWithSubscriptVisitor.found()) {
                SymbolicReference instanceReference = findReferenceWithSubscriptVisitor.getTheReference();
                // TODO multiple subscripts
                Expression subscript = instanceReference.getSubscripts().get(0);
                // Add branches based on the instance reference we found
                ArrayTypeDeclaration array = (ArrayTypeDeclaration)
                        state.theProgram.getLocalScope().getVariable(instanceReference).getTypeDeclaration();
                // TODO multiple ranges
                Range range = array.getRanges().get(0);
                RangeType rangeType = new RangeType(range.getStartValue(), range.getStopValue(), DataTypes.USINT);
                int rangeMin = Integer.parseInt(range.getStart().getText());
                for (int i = rangeMin; i <= Integer.parseInt(range.getStop().getText()); i++) {
                    StatementList block = new StatementList(statement.copy());
                    block.accept(new ArrayAccessRenameVisitor(instanceReference.getIdentifier(), i));
                    branch.addGuardedCommand(new GuardedStatement(
                            BinaryExpression.equalsExpression(subscript, new Literal(rangeType, Integer.toString(i))),
                            block));
                }
                // Perform search once more
                findReferenceWithSubscriptVisitor.reset();
            }
            if (branch.getConditionalBranches().isEmpty())
                // Keep statements intact we case we don't find anything to rename
                return statement;
            else if (branch.getConditionalBranches().size() == 1)
                // Only one condition branch, no need for IF
                return branch.getConditionalBranches().get(0).getStatements().get(0);
            else
                return branch;
        }

        @Override
        public Object visit(StatementList statements) {
            StatementList statementList = new StatementList();
            for (Statement statement : statements) {
                // We need to handle guarded statements differently since the guard cannot contain another if statement
                if (statement instanceof IfStatement) {
                    IfStatement ifStatement = (IfStatement) statement;
                    IfStatement newIfStatement = new IfStatement();
                    for (GuardedStatement guardedStatement : ifStatement.getConditionalBranches())
                        newIfStatement.addGuardedCommand(guardedStatement.getCondition(),
                                (StatementList) guardedStatement.getStatements().accept(this));
                    newIfStatement.setElseBranch((StatementList) ifStatement.getElseBranch().accept(this));
                    statement = newIfStatement;
                } else if (statement instanceof GuardedStatement) {
                    GuardedStatement guardedStatement = (GuardedStatement) statement;
                    guardedStatement.setStatements((StatementList) guardedStatement.getStatements().accept(this));
                    statement = guardedStatement;
                }
                statementList.add((Statement) visit(statement));
            }
            return statementList;
        }

        @Getter
        private class FindReferenceWithSubscriptVisitor extends AstVisitor {
            private SymbolicReference theReference;

            boolean found() {
                return theReference != null;
            }

            @Override
            public Object defaultVisit(Visitable visitable) {
                if (found())
                    return null;
                return super.defaultVisit(visitable);
            }

            @Override
            public Object visit(SymbolicReference symbolicReference) {
                if (found())
                    return null;
                if (symbolicReference.getIdentifier().equals(arrayVariable.getIdentifier())
                        && symbolicReference.hasSubscripts())
                    theReference = symbolicReference;
                if (symbolicReference.hasSub())
                    symbolicReference.getSub().accept(this);
                if (symbolicReference.hasSubscripts())
                    symbolicReference.getSubscripts().accept(this);
                return super.visit(symbolicReference);
            }

            void reset() {
                theReference = null;
            }
        }
    }
}
