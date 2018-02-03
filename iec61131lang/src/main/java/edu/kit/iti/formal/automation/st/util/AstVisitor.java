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

import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.sfclang.ast.SFCAction;
import edu.kit.iti.formal.automation.sfclang.ast.SFCNetwork;
import edu.kit.iti.formal.automation.sfclang.ast.SFCStep;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import edu.kit.iti.formal.automation.visitors.Visitable;

import java.util.ArrayList;

/**
 * Created by weigl on 10/07/14.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
public class AstVisitor<T> extends DefaultVisitor<T> {
    protected TopLevelScopeElement currentTopLevelScopeElement;

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
        currentTopLevelScopeElement = programDeclaration;
        programDeclaration.getScope().accept(this);
        programDeclaration.getStBody().accept(this);
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
        currentTopLevelScopeElement = functionDeclaration;
        functionDeclaration.getScope().accept(this);
        functionDeclaration.getStBody().accept(this);
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
        functionBlockDeclaration.getScope().accept(this);
        functionBlockDeclaration.getStBody().accept(this);
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
    public T visit(Scope localScope) {
        for (VariableDeclaration vd : localScope.asMap().values())
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
        currentTopLevelScopeElement = clazz;
        clazz.getScope().accept(this);
        for (MethodDeclaration m : new ArrayList<>(clazz.getMethods())) {
            m.accept(this);
        }
        return super.visit(clazz);
    }

    @Override
    public T visit(InterfaceDeclaration interfaceDeclaration) {
        currentTopLevelScopeElement = interfaceDeclaration;
        interfaceDeclaration.getScope().accept(this);
        for (MethodDeclaration m : interfaceDeclaration.getMethods())
            m.accept(this);
        return super.visit(interfaceDeclaration);
    }

    @Override
    public T visit(MethodDeclaration method) {
        method.getScope().accept(this);
        if (method.getStBody() != null)
            method.getStBody().accept(this);
        return null;
    }

    @Override
    public T visit(GlobalVariableListDeclaration globalVariableListDeclaration) {
        currentTopLevelScopeElement = globalVariableListDeclaration;
        globalVariableListDeclaration.getScope().accept(this);
        return super.visit(globalVariableListDeclaration);
    }

    @Override
    public T visit(ArrayTypeDeclaration arrayTypeDeclaration) {
        return super.visit(arrayTypeDeclaration);
    }

    @Override
    public T visit(ExitStatement exitStatement) {
        return super.visit(exitStatement);
    }

    @Override
    public T visit(ConfigurationDeclaration configurationDeclaration) {
        return super.visit(configurationDeclaration);
    }

    @Override
    public T visit(EnumerationTypeDeclaration enumerationTypeDeclaration) {
        return super.visit(enumerationTypeDeclaration);
    }

    @Override
    public T visit(ResourceDeclaration resourceDeclaration) {
        return super.visit(resourceDeclaration);
    }

    @Override
    public T visit(ReturnStatement returnStatement) {
        return super.visit(returnStatement);
    }

    @Override
    public T visit(Deref deref) {
        return super.visit(deref);
    }

    @Override
    public T visit(SymbolicReference symbolicReference) {
        return super.visit(symbolicReference);
    }

    @Override
    public T visit(PointerTypeDeclaration ptd) {
        return super.visit(ptd);
    }

    @Override
    public T visit(IdentifierInitializer init) {
        return super.visit(init);
    }

    @Override
    public T visit(Literal literal) {
        return super.visit(literal);
    }

    @Override
    public T visit(ReferenceSpecification referenceSpecification) {
        return super.visit(referenceSpecification);
    }

    @Override
    public T visit(SFCStep sfcStep) {
        return super.visit(sfcStep);
    }

    @Override
    public T visit(SFCAction sfcAction) {
        return super.visit(sfcAction);
    }

    @Override
    public T visit(SFCNetwork sfcNetwork) {
        return super.visit(sfcNetwork);
    }
}
