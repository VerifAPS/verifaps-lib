package edu.kit.iti.formal.automation.st.util;

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

import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import edu.kit.iti.formal.automation.visitors.Visitable;

/**
 * Created by weigl on 10/07/14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class AstVisitor<T> extends DefaultVisitor<T> {
    /**
     * {@inheritDoc}
     */
    @Override
    public T defaultVisit(Visitable visitable) {
        return null;//throw new Error("not implemented for " + visitable.getClass());
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(AssignmentStatement assignmentStatement) {
        assignmentStatement.getExpression().accept(this);
        assignmentStatement.getLocation().accept(this);
        return null;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(CaseCondition.Range range) {
        range.getStart().accept(this);
        range.getStop().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(CaseCondition.IntegerCondition integerCondition) {
        integerCondition.getValue().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(CaseCondition.Enumeration enumeration) {
        enumeration.getStart().accept(this);
        enumeration.getStop().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(BinaryExpression binaryExpression) {
        binaryExpression.getLeftExpr().accept(this);
        binaryExpression.getRightExpr().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(RepeatStatement repeatStatement) {
        repeatStatement.getCondition().accept(this);
        repeatStatement.getStatements().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(WhileStatement whileStatement) {
        whileStatement.getCondition().accept(this);
        whileStatement.getStatements().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(UnaryExpression unaryExpression) {
        unaryExpression.getExpression().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(TypeDeclarations typeDeclarations) {
        for (TypeDeclaration td : typeDeclarations)
            td.accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(CaseStatement caseStatement) {
        caseStatement.getExpression().accept(this);
        for (CaseStatement.Case c : caseStatement.getCases())
            c.accept(this);

        caseStatement.getElseCase().accept(this);

        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(StatementList statements) {
        for (Statement s : statements)
            if (s != null)
                s.accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(ProgramDeclaration programDeclaration) {
        programDeclaration.getLocalScope().accept(this);
        programDeclaration.getProgramBody().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(ExpressionList expressions) {
        for (Expression e : expressions)
            e.accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(FunctionDeclaration functionDeclaration) {
        functionDeclaration.getLocalScope().accept(this);
        functionDeclaration.getStatements().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(ForStatement forStatement) {
        forStatement.getStart().accept(this);
        if (forStatement.getStep() != null)
            forStatement.getStep().accept(this);
        forStatement.getStop().accept(this);
        forStatement.getStatements().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(FunctionBlockDeclaration functionBlockDeclaration) {
        functionBlockDeclaration.getLocalScope().accept(this);
        functionBlockDeclaration.getFunctionBody().accept(this);
        return null;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(IfStatement ifStatement) {
        for (GuardedStatement gs : ifStatement.getConditionalBranches())
            gs.accept(this);

        ifStatement.getElseBranch().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(GuardedStatement guardedStatement) {
        guardedStatement.getCondition().accept(this);
        guardedStatement.getStatements().accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(CaseStatement.Case aCase) {
        aCase.getStatements().accept(this);
        for (CaseCondition c : aCase.getConditions())
            c.accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(LocalScope localScope) {
        for (VariableDeclaration vd : localScope.getLocalVariables().values())
            vd.accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(VariableDeclaration variableDeclaration) {
        return super.visit(variableDeclaration);
    }

    @Override
    public T visit(Location location) {
        return super.visit(location);
    }

    @Override
    public T visit(ArrayInitialization initializations) {
        for (Initialization init : initializations)
            init.accept(this);
        return super.visit(initializations);
    }

    @Override
    public T visit(Invocation invocation) {
        invocation.getParameters().forEach(e -> e.accept(this));
        return super.visit(invocation);
    }

    @Override
    public T visit(InvocationStatement fbc) {
        fbc.getInvocation().accept(this);
        return super.visit(fbc);
    }

    @Override
    public T visit(Invocation.Parameter parameter) {
        parameter.getExpression().accept(this);
        return super.visit(parameter);
    }

    @Override
    public T visit(StringTypeDeclaration stringTypeDeclaration) {
        stringTypeDeclaration.getInitialization().accept(this);
        return super.visit(stringTypeDeclaration);
    }

    @Override
    public T visit(StructureTypeDeclaration structureTypeDeclaration) {
        return super.visit(structureTypeDeclaration);
    }

    @Override
    public T visit(SubRangeTypeDeclaration subRangeTypeDeclaration) {
        return super.visit(subRangeTypeDeclaration);
    }

    @Override
    public T visit(SimpleTypeDeclaration simpleTypeDeclaration) {
        return super.visit(simpleTypeDeclaration);
    }

    @Override
    public T visit(CommentStatement commentStatement) {
        return super.visit(commentStatement);
    }

    @Override
    public T visit(StructureInitialization structureInitialization) {
        structureInitialization.getInitValues().values().forEach(v -> v.accept(this));
        return super.visit(structureInitialization);
    }

    @Override
    public T visit(ClassDeclaration clazz) {
        clazz.getLocalScope().accept(this);
        for (MethodDeclaration m : clazz.getMethods()) {
            m.accept(this);
        }
        return super.visit(clazz);
    }

    @Override
    public T visit(MethodDeclaration method) {
        method.getLocalScope().accept(this);
        method.getStatements().accept(this);
        return null;
    }


}
