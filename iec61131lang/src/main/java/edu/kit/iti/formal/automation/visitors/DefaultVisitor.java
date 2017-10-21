package edu.kit.iti.formal.automation.visitors;

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
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.st.ast.*;

/**
 * Created by weigl on 21.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class DefaultVisitor<T> implements Visitor<T> {

    /**
     * <p>defaultVisit.</p>
     *
     * @param visitable a {@link edu.kit.iti.formal.automation.visitors.Visitable} object.
     * @return a T object.
     */
    public T defaultVisit(Visitable visitable) {
        //return visitable.accept(this);
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(Location location) {
        return defaultVisit(location);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(ArrayInitialization initializations) {
        return defaultVisit(initializations);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(ArrayTypeDeclaration arrayTypeDeclaration) {
        return defaultVisit(arrayTypeDeclaration);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(AssignmentStatement assignmentStatement) {
        return defaultVisit(assignmentStatement);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(ExitStatement exitStatement) {
        return defaultVisit(exitStatement);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(CaseCondition.Range range) {
        return defaultVisit(range);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(CaseCondition.IntegerCondition integerCondition) {
        return defaultVisit(integerCondition);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(CaseCondition.Enumeration enumeration) {
        return defaultVisit(enumeration);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(BinaryExpression binaryExpression) {
        return defaultVisit(binaryExpression);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(ConfigurationDeclaration configurationDeclaration) {
        return defaultVisit(configurationDeclaration);
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(EnumerationTypeDeclaration enumerationTypeDeclaration) {
        return defaultVisit(enumerationTypeDeclaration);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(RepeatStatement repeatStatement) {
        return defaultVisit(repeatStatement);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(WhileStatement whileStatement) {
        return defaultVisit(whileStatement);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(UnaryExpression unaryExpression) {
        return defaultVisit(unaryExpression);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(TypeDeclarations typeDeclarations) {
        return defaultVisit(typeDeclarations);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(CaseStatement caseStatement) {
        return defaultVisit(caseStatement);
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(StatementList statements) {
        return defaultVisit(statements);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(ProgramDeclaration programDeclaration) {
        return defaultVisit(programDeclaration);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(ExpressionList expressions) {
        return defaultVisit(expressions);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(FunctionDeclaration functionDeclaration) {
        return defaultVisit(functionDeclaration);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(FunctionCall functionCall) {
        return defaultVisit(functionCall);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(ForStatement forStatement) {
        return defaultVisit(forStatement);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(ResourceDeclaration resourceDeclaration) {
        return defaultVisit(resourceDeclaration);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(FunctionBlockDeclaration functionBlockDeclaration) {
        return defaultVisit(functionBlockDeclaration);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(ReturnStatement returnStatement) {
        return defaultVisit(returnStatement);
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(IfStatement ifStatement) {
        return defaultVisit(ifStatement);
    }

    /**
     * {@inheritDoc}
     */
    public T visit(GuardedStatement guardedStatement) {
        return defaultVisit(guardedStatement);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(FunctionBlockCallStatement fbc) {
        return defaultVisit(fbc);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(CaseStatement.Case aCase) {
        return defaultVisit(aCase);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(StringTypeDeclaration stringTypeDeclaration) {
        return defaultVisit(stringTypeDeclaration);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(StructureTypeDeclaration structureTypeDeclaration) {
        return defaultVisit(structureTypeDeclaration);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(SubRangeTypeDeclaration subRangeTypeDeclaration) {
        return defaultVisit(subRangeTypeDeclaration);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(SimpleTypeDeclaration simpleTypeDeclaration) {
        return defaultVisit(simpleTypeDeclaration);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(LocalScope localScope) {
        return defaultVisit(localScope);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(VariableDeclaration variableDeclaration) {
        return defaultVisit(variableDeclaration);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(CommentStatement commentStatement) {
        return defaultVisit(commentStatement);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(StructureInitialization structureInitialization) {
        return defaultVisit(structureInitialization);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(Deref deref) {
        return defaultVisit(deref);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(SymbolicReference symbolicReference) {
        return defaultVisit(symbolicReference);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(PointerTypeDeclaration ptd) {
        return defaultVisit(ptd);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public T visit(IdentifierInitializer init) {
        return defaultVisit(init);
    }

    @Override
    public T visit(InterfaceDeclaration interfaceDeclaration) {
        return defaultVisit(interfaceDeclaration);
    }

    @Override
    public T visit(ClassDeclaration clazz) {
        return defaultVisit(clazz);
    }

    @Override
    public T visit(MethodDeclaration method) {
        return defaultVisit(method);
    }

    @Override
    public T visit(Literal literal) {
        return defaultVisit(literal);
    }

    @Override
    public T visit(FunctionBlockCallStatement.Parameter parameter) {
        return null;
    }
}
