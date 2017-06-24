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
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import edu.kit.iti.formal.automation.visitors.Visitable;
import edu.kit.iti.formal.automation.st.ast.*;

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
        assignmentStatement.getExpression().visit(this);
        assignmentStatement.getLocation().visit(this);
        return null;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(CaseCondition.Range range) {
        range.getStart().visit(this);
        range.getStop().visit(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(CaseCondition.IntegerCondition integerCondition) {
        integerCondition.getValue().visit(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(CaseCondition.Enumeration enumeration) {
        enumeration.getStart().visit(this);
        enumeration.getStop().visit(this);

        return null;

    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(BinaryExpression binaryExpression) {
        binaryExpression.getLeftExpr().visit(this);
        binaryExpression.getRightExpr().visit(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(RepeatStatement repeatStatement) {
        repeatStatement.getCondition().visit(this);
        repeatStatement.getStatements().visit(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(WhileStatement whileStatement) {
        whileStatement.getCondition().visit(this);
        whileStatement.getStatements().visit(this);

        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(UnaryExpression unaryExpression) {
        unaryExpression.getExpression().visit(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(TypeDeclarations typeDeclarations) {
        for (TypeDeclaration td : typeDeclarations)
            td.visit(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(CaseStatement caseStatement) {
        caseStatement.getExpression().visit(this);
        for (CaseStatement.Case c : caseStatement.getCases())
            c.visit(this);

        caseStatement.getElseCase().visit(this);

        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(StatementList statements) {
        for (Statement s : statements)
            s.visit(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(ProgramDeclaration programDeclaration) {
        programDeclaration.getProgramBody().visit(this);
        programDeclaration.getLocalScope().visit(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(ExpressionList expressions) {
        for (Expression e : expressions)
            e.visit(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(FunctionDeclaration functionDeclaration) {
        functionDeclaration.getLocalScope().visit(this);
        functionDeclaration.getStatements().visit(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(ForStatement forStatement) {
        forStatement.getStart().visit(this);
        if (forStatement.getStep() != null)
            forStatement.getStep().visit(this);
        forStatement.getStop().visit(this);
        forStatement.getStatements().visit(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(FunctionBlockDeclaration functionBlockDeclaration) {
        functionBlockDeclaration.getFunctionBody().visit(this);
        functionBlockDeclaration.getLocalScope().visit(this);
        return null;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(IfStatement ifStatement) {
        for (GuardedStatement gs : ifStatement.getConditionalBranches())
            gs.visit(this);

        ifStatement.getElseBranch().visit(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(GuardedStatement guardedStatement) {
        guardedStatement.getCondition().visit(this);
        guardedStatement.getStatements().visit(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(CaseStatement.Case aCase) {
        aCase.getStatements().visit(this);
        for (CaseCondition c : aCase.getConditions())
            c.visit(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(LocalScope localScope) {
        for (VariableDeclaration vd : localScope.getLocalVariables().values())
            vd.visit(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(VariableDeclaration variableDeclaration) {
        return super.visit(variableDeclaration);
    }
}
