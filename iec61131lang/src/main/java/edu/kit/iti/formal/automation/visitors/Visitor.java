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
import edu.kit.iti.formal.automation.st.ast.*;

/**
 * Created by weigla on 14.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
public interface Visitor<T> {
    /**
     * <p>accept.</p>
     *
     * @param location a {@link edu.kit.iti.formal.automation.st.ast.Location} object.
     * @return a T object.
     */
    T visit(Location location);

    /**
     * <p>accept.</p>
     *
     * @param initializations a {@link edu.kit.iti.formal.automation.st.ast.ArrayInitialization} object.
     * @return a T object.
     */
    T visit(ArrayInitialization initializations);

    /**
     * <p>accept.</p>
     *
     * @param arrayTypeDeclaration a {@link edu.kit.iti.formal.automation.st.ast.ArrayTypeDeclaration} object.
     * @return a T object.
     */
    T visit(ArrayTypeDeclaration arrayTypeDeclaration);

    /**
     * <p>accept.</p>
     *
     * @param assignmentStatement a {@link edu.kit.iti.formal.automation.st.ast.AssignmentStatement} object.
     * @return a T object.
     */
    T visit(AssignmentStatement assignmentStatement);

    /**
     * <p>accept.</p>
     *
     * @param exitStatement a {@link edu.kit.iti.formal.automation.st.ast.ExitStatement} object.
     * @return a T object.
     */
    T visit(ExitStatement exitStatement);

    /**
     * <p>accept.</p>
     *
     * @param range a {@link CaseCondition.Range} object.
     * @return a T object.
     */
    T visit(CaseCondition.Range range);

    /**
     * <p>accept.</p>
     *
     * @param integerCondition a {@link CaseCondition.IntegerCondition} object.
     * @return a T object.
     */
    T visit(CaseCondition.IntegerCondition integerCondition);

    /**
     * <p>accept.</p>
     *
     * @param enumeration a {@link CaseCondition.Enumeration} object.
     * @return a T object.
     */
    T visit(CaseCondition.Enumeration enumeration);

    /**
     * <p>accept.</p>
     *
     * @param binaryExpression a {@link edu.kit.iti.formal.automation.st.ast.BinaryExpression} object.
     * @return a T object.
     */
    T visit(BinaryExpression binaryExpression);

    /**
     * <p>accept.</p>
     *
     * @param configurationDeclaration a {@link edu.kit.iti.formal.automation.st.ast.ConfigurationDeclaration} object.
     * @return a T object.
     */
    T visit(ConfigurationDeclaration configurationDeclaration);

    //T accept(DirectVariable directVariable);

    /**
     * <p>accept.</p>
     *
     * @param enumerationTypeDeclaration a {@link edu.kit.iti.formal.automation.st.ast.EnumerationTypeDeclaration} object.
     * @return a T object.
     */
    T visit(EnumerationTypeDeclaration enumerationTypeDeclaration);

    /**
     * <p>accept.</p>
     *
     * @param repeatStatement a {@link edu.kit.iti.formal.automation.st.ast.RepeatStatement} object.
     * @return a T object.
     */
    T visit(RepeatStatement repeatStatement);

    /**
     * <p>accept.</p>
     *
     * @param whileStatement a {@link edu.kit.iti.formal.automation.st.ast.WhileStatement} object.
     * @return a T object.
     */
    T visit(WhileStatement whileStatement);

    /**
     * <p>accept.</p>
     *
     * @param unaryExpression a {@link edu.kit.iti.formal.automation.st.ast.UnaryExpression} object.
     * @return a T object.
     */
    T visit(UnaryExpression unaryExpression);

    /**
     * <p>accept.</p>
     *
     * @param typeDeclarations a {@link edu.kit.iti.formal.automation.st.ast.TypeDeclarations} object.
     * @return a T object.
     */
    T visit(TypeDeclarations typeDeclarations);

    /**
     * <p>accept.</p>
     *
     * @param caseStatement a {@link edu.kit.iti.formal.automation.st.ast.CaseStatement} object.
     * @return a T object.
     */
    T visit(CaseStatement caseStatement);

    //T accept(SymbolicReference symbolicReference);

    /**
     * <p>accept.</p>
     *
     * @param statements a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     * @return a T object.
     */
    T visit(StatementList statements);

    /**
     * <p>accept.</p>
     *
     * @param programDeclaration a {@link edu.kit.iti.formal.automation.st.ast.ProgramDeclaration} object.
     * @return a T object.
     */
    T visit(ProgramDeclaration programDeclaration);


    /**
     * <p>accept.</p>
     *
     * @param expressions a {@link edu.kit.iti.formal.automation.st.ast.ExpressionList} object.
     * @return a T object.
     */
    T visit(ExpressionList expressions);

    /**
     * <p>accept.</p>
     *
     * @param functionDeclaration a {@link edu.kit.iti.formal.automation.st.ast.FunctionDeclaration} object.
     * @return a T object.
     */
    T visit(FunctionDeclaration functionDeclaration);

    /**
     * <p>accept.</p>
     *
     * @param invocation a {@link Invocation} object.
     * @return a T object.
     */
    T visit(Invocation invocation);

    /**
     * <p>accept.</p>
     *
     * @param forStatement a {@link edu.kit.iti.formal.automation.st.ast.ForStatement} object.
     * @return a T object.
     */
    T visit(ForStatement forStatement);

    /**
     * <p>accept.</p>
     *
     * @param resourceDeclaration a {@link edu.kit.iti.formal.automation.st.ast.ResourceDeclaration} object.
     * @return a T object.
     */
    T visit(ResourceDeclaration resourceDeclaration);

    /**
     * <p>accept.</p>
     *
     * @param functionBlockDeclaration a {@link edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration} object.
     * @return a T object.
     */
    T visit(FunctionBlockDeclaration functionBlockDeclaration);

    /**
     * <p>accept.</p>
     *
     * @param returnStatement a {@link edu.kit.iti.formal.automation.st.ast.ReturnStatement} object.
     * @return a T object.
     */
    T visit(ReturnStatement returnStatement);

    /**
     * <p>accept.</p>
     *
     * @param ifStatement a {@link edu.kit.iti.formal.automation.st.ast.IfStatement} object.
     * @return a T object.
     */
    T visit(IfStatement ifStatement);

    /**
     * <p>accept.</p>
     *
     * @param guardedStatement a {@link edu.kit.iti.formal.automation.st.ast.GuardedStatement} object.
     * @return a T object.
     */
    T visit(GuardedStatement guardedStatement);

    /**
     * <p>accept.</p>
     *
     * @param invocationStatement a {@link InvocationStatement} object.
     * @return a T object.
     */
    T visit(InvocationStatement invocationStatement);

    /**
     * <p>accept.</p>
     *
     * @param aCase a {@link edu.kit.iti.formal.automation.st.ast.CaseStatement.Case} object.
     * @return a T object.
     */
    T visit(CaseStatement.Case aCase);

    /**
     * <p>accept.</p>
     *
     * @param stringTypeDeclaration a {@link edu.kit.iti.formal.automation.st.ast.StringTypeDeclaration} object.
     * @return a T object.
     */
    T visit(StringTypeDeclaration stringTypeDeclaration);

    /**
     * <p>accept.</p>
     *
     * @param structureTypeDeclaration a {@link edu.kit.iti.formal.automation.st.ast.StructureTypeDeclaration} object.
     * @return a T object.
     */
    T visit(StructureTypeDeclaration structureTypeDeclaration);

    /**
     * <p>accept.</p>
     *
     * @param subRangeTypeDeclaration a {@link edu.kit.iti.formal.automation.st.ast.SubRangeTypeDeclaration} object.
     * @return a T object.
     */
    T visit(SubRangeTypeDeclaration subRangeTypeDeclaration);

    /**
     * <p>accept.</p>
     *
     * @param simpleTypeDeclaration a {@link edu.kit.iti.formal.automation.st.ast.SimpleTypeDeclaration} object.
     * @return a T object.
     */
    T visit(SimpleTypeDeclaration simpleTypeDeclaration);

    /**
     * <p>accept.</p>
     *
     * @param localScope a {@link edu.kit.iti.formal.automation.scope.LocalScope} object.
     * @return a T object.
     */
    T visit(LocalScope localScope);

    /**
     * <p>accept.</p>
     *
     * @param variableDeclaration a {@link edu.kit.iti.formal.automation.st.ast.VariableDeclaration} object.
     * @return a T object.
     */
    T visit(VariableDeclaration variableDeclaration);

    /**
     * <p>accept.</p>
     *
     * @param commentStatement a {@link edu.kit.iti.formal.automation.st.ast.CommentStatement} object.
     * @return a T object.
     */
    T visit(CommentStatement commentStatement);

    /**
     * <p>accept.</p>
     *
     * @param structureInitialization a {@link edu.kit.iti.formal.automation.st.ast.StructureInitialization} object.
     * @return a T object.
     */
    T visit(StructureInitialization structureInitialization);

    /**
     * <p>accept.</p>
     *
     * @param deref a {@link edu.kit.iti.formal.automation.st.ast.Deref} object.
     * @return a T object.
     */
    T visit(Deref deref);

    /**
     * <p>accept.</p>
     *
     * @param symbolicReference a {@link edu.kit.iti.formal.automation.st.ast.SymbolicReference} object.
     * @return a T object.
     */
    T visit(SymbolicReference symbolicReference);

    /**
     * <p>accept.</p>
     *
     * @param ptd a {@link edu.kit.iti.formal.automation.st.ast.PointerTypeDeclaration} object.
     * @return a T object.
     */
    T visit(PointerTypeDeclaration ptd);

    /**
     * <p>accept.</p>
     *
     * @param init a {@link edu.kit.iti.formal.automation.st.ast.IdentifierInitializer} object.
     * @return a T object.
     */
    T visit(IdentifierInitializer init);

    T visit(InterfaceDeclaration interfaceDeclaration);

    T visit(ClassDeclaration clazz);

    T visit(MethodDeclaration method);

    T visit(Literal literal);

    T visit(Invocation.Parameter parameter);

    T visit(ReferenceSpecification referenceSpecification);
}
