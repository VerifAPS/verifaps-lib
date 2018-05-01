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

import edu.kit.iti.formal.automation.datatypes.ClassDataType;
import edu.kit.iti.formal.automation.datatypes.DataTypes;
import edu.kit.iti.formal.automation.datatypes.RangeType;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import edu.kit.iti.formal.automation.st0.STSimplifier;
import edu.kit.iti.formal.automation.visitors.Visitable;
import lombok.AllArgsConstructor;
import lombok.Getter;
import lombok.RequiredArgsConstructor;

import java.util.HashSet;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Created by weigl on 03/10/14.
 * @author Alexander Weigl, Augusto Modanese
 */
public class ArrayEmbedder implements ST0Transformation {
    private STSimplifier.State state;
    private long instanceCount = 0;

    @Override
    public void transform(STSimplifier.State state) {
        this.state = state;
        for (VariableDeclaration arrayVariable : state.theProgram.getScope().stream()
                .filter(v -> v.getTypeDeclaration() instanceof ArrayTypeDeclaration)
                .collect(Collectors.toList())) {
            ArrayTypeDeclaration array = (ArrayTypeDeclaration) arrayVariable.getTypeDeclaration();
            assert array.getInitialization() != null;
            for (Range range : array.getRanges()) {
                int rangeMin = Integer.parseInt(range.getStart().getText());
                int rangeMax = Integer.parseInt(range.getStop().getText());
                // TODO multiple ranges
                for (int i = rangeMin; i <= rangeMax; i++) {
                    VariableDeclaration var = new VariableDeclaration(
                            arrayVariable.getIdentifier() + "$" + i,
                            new SimpleTypeDeclaration<>(array.getBaseType(),
                                    array.getInitialization().get(i - rangeMin)));
                    if (arrayVariable.isGlobal()) {
                        var.setType(VariableDeclaration.GLOBAL);
                        state.theProgram.getScope().add(var);
                    }
                }
                ArrayEmbedderVisitor arrayEmbedderVisitor = new ArrayEmbedderVisitor(arrayVariable);
                state.functions.values().forEach(f -> f.accept(arrayEmbedderVisitor));
                state.theProgram.accept(arrayEmbedderVisitor);
                state.functions.values().forEach(f -> f.accept(arrayEmbedderVisitor));
                state.theProgram.accept(arrayEmbedderVisitor);
                state.theProgram.getScope().asMap().remove(arrayVariable.getName());
            }
            //System.out.println("Counted " + instanceCount + " instances");
        }
    }

    @Getter
    @AllArgsConstructor
    private static class ArrayAccessRenameVisitor extends AstMutableVisitor {
        /**
         * Name of the array which is accessed.
         */
        private final String toRename;
        /**
         * Index to be accessed.
         */
        private final int access;
        /**
         * Subscript, i.e., the value of the index being accessed.
         */
        private final Expression subscript;

        @Override
        public Object visit(SymbolicReference symbolicReference) {
            if (symbolicReference.getIdentifier().equals(toRename) && symbolicReference.hasSubscripts()) {
                symbolicReference.setIdentifier(toRename + "$" + access);
                symbolicReference.setSubscripts(null);
            }
            // Set constant value for subscript (if it is a symbolic reference)
            else if (subscript instanceof SymbolicReference && symbolicReference.equals(subscript))
                return Literal.integer(access);
            return super.visit(symbolicReference);
        }
    }

    @Getter
    @AllArgsConstructor
    private class ArrayEmbedderVisitor extends AstMutableVisitor {
        private final VariableDeclaration arrayVariable;

        @Override
        public Object visit(StatementList statements) {
            // First branch the entire code block for read-only variables
            Object newStatements = findAndBranch(statements, new FindReferenceWithSubscriptVisitor(
                    symbolicReference -> {
                        if (!(symbolicReference.getIdentifiedObject() instanceof VariableDeclaration))
                            return false;
                        VariableDeclaration var = (VariableDeclaration) symbolicReference.getIdentifiedObject();
                        return var.isInput();
                    }));
            assert newStatements instanceof Statement || newStatements instanceof StatementList;
            statements = newStatements instanceof Statement
                    ? new StatementList((Statement) newStatements)
                    : (StatementList) newStatements;
            // Now the rest
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
                } else if (statement instanceof CaseStatement) {
                    CaseStatement caseStatement = (CaseStatement) statement;
                    CaseStatement newCaseStatement = new CaseStatement();
                    newCaseStatement.setExpression(caseStatement.getExpression());
                    for (CaseStatement.Case c : caseStatement.getCases())
                        newCaseStatement.addCase(new CaseStatement.Case(
                                c.getConditions(), (StatementList) c.getStatements().accept(this)
                        ));
                    newCaseStatement.setElseCase((StatementList) caseStatement.getElseCase().accept(this));
                    statement = newCaseStatement;
                } else if (statement instanceof GuardedStatement) {
                    GuardedStatement guardedStatement = (GuardedStatement) statement;
                    guardedStatement.setStatements((StatementList) guardedStatement.getStatements().accept(this));
                    //statement = guardedStatement;
                }
                statementList.add((Statement) findAndBranch(statement, new FindReferenceWithSubscriptVisitor()));
            }
            return statementList;
        }

        private Object findAndBranch(Visitable codeBlock, FindReferenceWithSubscriptVisitor subscriptFinder) {
            assert codeBlock instanceof Statement || codeBlock instanceof StatementList;
            codeBlock.accept(subscriptFinder);
            IfStatement branch = new IfStatement();
            while (subscriptFinder.found()) {
                SymbolicReference instanceReference = subscriptFinder.getTheReference();
                // TODO multiple subscripts
                Expression subscript = instanceReference.getSubscripts().get(0);
                // Add branches based on the instance reference we found
                ArrayTypeDeclaration array = (ArrayTypeDeclaration)
                        state.theProgram.getScope().getVariable(instanceReference).getTypeDeclaration();
                // TODO multiple ranges
                Range range = array.getRanges().get(0);
                RangeType rangeType = new RangeType(range.getStartValue(), range.getStopValue(), DataTypes.USINT);
                Set<Integer> values = new HashSet<>();
                if (subscript instanceof SymbolicReference) {
                    SymbolicReference r = (SymbolicReference) subscript;
                    while (r.hasSub())
                        r = r.getSub();
                    if (r.getIdentifiedObject() instanceof VariableDeclaration) {
                        VariableDeclaration variable = (VariableDeclaration) r.getIdentifiedObject();
                        if (!(state.stooState.getInstancesOfVariable(variable).isEmpty()))
                            state.stooState.getInstancesOfVariable(variable).parallelStream()
                                    .map(i -> state.stooState.getInstanceID(i))
                                    .forEach(values::add);
                        else
                            try {
                                state.stooState.getEffectiveSubtypeScope()
                                        .getTypes(variable).parallelStream()
                                        .map(t -> state.stooState.getInstanceIDRangesToClass(
                                                ((ClassDataType) t).getClazz()))
                                        .forEach(pairs -> pairs.parallelStream()
                                                .forEach(p -> IntStream.range(p.a, p.b + 1)
                                                        .forEach(values::add)));
                            } catch (NoSuchElementException ignored) {
                            }
                    }
                }
                if (values.isEmpty()) {
                    int rangeMin = Integer.parseInt(range.getStart().getText());
                    for (int i = rangeMin; i <= Integer.parseInt(range.getStop().getText()); i++)
                        values.add(i);
                }
                instanceCount += values.size();
                for (int i : values) {
                    StatementList block = codeBlock instanceof Statement
                            ? new StatementList((Statement) ((Statement) codeBlock).copy())
                            : new StatementList(((StatementList) codeBlock).copy());
                    block.accept(new ArrayAccessRenameVisitor(instanceReference.getIdentifier(), i, subscript));
                    branch.addGuardedCommand(new GuardedStatement(
                            BinaryExpression.equalsExpression(subscript, new Literal(rangeType, Integer.toString(i))),
                            block));
                }
                // Perform search once more
                subscriptFinder.reset();
            }
            if (branch.getConditionalBranches().isEmpty())
                // Keep statements intact we case we don't find anything to rename
                return codeBlock;
            else if (branch.getConditionalBranches().size() == 1)
                // Only one condition branch, no need for IF
                return branch.getConditionalBranches().get(0).getStatements().get(0);
            else
                return branch;
        }

        @Getter
        @RequiredArgsConstructor
        private class FindReferenceWithSubscriptVisitor extends AstVisitor<Object> {
            private final Function<SymbolicReference, Boolean> match;
            private SymbolicReference theReference;

            FindReferenceWithSubscriptVisitor() {
                match = symbolicReference -> true;
            }

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
                // TODO multiple subscripts
                if (symbolicReference.getIdentifier().equals(arrayVariable.getIdentifier())
                        && symbolicReference.hasSubscripts()
                        && symbolicReference.getSubscripts().get(0) instanceof SymbolicReference
                        && match.apply((SymbolicReference) symbolicReference.getSubscripts().get(0)))
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
