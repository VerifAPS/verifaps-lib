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
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.ast.ArrayInitialization;

/**
 * Created by weigla on 14.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
public interface Visitor<T> {
    /**
     * <p>visit.</p>
     *
     * @param location a {@link edu.kit.iti.formal.automation.st.ast.Location} object.
     * @return a T object.
     */
    T visit(Location location);

    /**
     * <p>visit.</p>
     *
     * @param initializations a {@link edu.kit.iti.formal.automation.st.ast.ArrayInitialization} object.
     * @return a T object.
     */
    T visit(ArrayInitialization initializations);

    /**
     * <p>visit.</p>
     *
     * @param arrayTypeDeclaration a {@link edu.kit.iti.formal.automation.st.ast.ArrayTypeDeclaration} object.
     * @return a T object.
     */
    T visit(ArrayTypeDeclaration arrayTypeDeclaration);

    /**
     * <p>visit.</p>
     *
     * @param assignmentStatement a {@link edu.kit.iti.formal.automation.st.ast.AssignmentStatement} object.
     * @return a T object.
     */
    T visit(AssignmentStatement assignmentStatement);

    /**
     * <p>visit.</p>
     *
     * @param exitStatement a {@link edu.kit.iti.formal.automation.st.ast.ExitStatement} object.
     * @return a T object.
     */
    T visit(ExitStatement exitStatement);

    /**
     * <p>visit.</p>
     *
     * @param range a {@link CaseCondition.Range} object.
     * @return a T object.
     */
    T visit(CaseCondition.Range range);

    /**
     * <p>visit.</p>
     *
     * @param integerCondition a {@link CaseCondition.IntegerCondition} object.
     * @return a T object.
     */
    T visit(CaseCondition.IntegerCondition integerCondition);

    /**
     * <p>visit.</p>
     *
     * @param enumeration a {@link CaseCondition.Enumeration} object.
     * @return a T object.
     */
    T visit(CaseCondition.Enumeration enumeration);

    /**
     * <p>visit.</p>
     *
     * @param binaryExpression a {@link edu.kit.iti.formal.automation.st.ast.BinaryExpression} object.
     * @return a T object.
     */
    T visit(BinaryExpression binaryExpression);

    /**
     * <p>visit.</p>
     *
     * @param configurationDeclaration a {@link edu.kit.iti.formal.automation.st.ast.ConfigurationDeclaration} object.
     * @return a T object.
     */
    T visit(ConfigurationDeclaration configurationDeclaration);

    //T visit(DirectVariable directVariable);

    /**
     * <p>visit.</p>
     *
     * @param enumerationTypeDeclaration a {@link edu.kit.iti.formal.automation.st.ast.EnumerationTypeDeclaration} object.
     * @return a T object.
     */
    T visit(EnumerationTypeDeclaration enumerationTypeDeclaration);

    /**
     * <p>visit.</p>
     *
     * @param repeatStatement a {@link edu.kit.iti.formal.automation.st.ast.RepeatStatement} object.
     * @return a T object.
     */
    T visit(RepeatStatement repeatStatement);

    /**
     * <p>visit.</p>
     *
     * @param whileStatement a {@link edu.kit.iti.formal.automation.st.ast.WhileStatement} object.
     * @return a T object.
     */
    T visit(WhileStatement whileStatement);

    /**
     * <p>visit.</p>
     *
     * @param unaryExpression a {@link edu.kit.iti.formal.automation.st.ast.UnaryExpression} object.
     * @return a T object.
     */
    T visit(UnaryExpression unaryExpression);

    /**
     * <p>visit.</p>
     *
     * @param typeDeclarations a {@link edu.kit.iti.formal.automation.st.ast.TypeDeclarations} object.
     * @return a T object.
     */
    T visit(TypeDeclarations typeDeclarations);

    /**
     * <p>visit.</p>
     *
     * @param caseStatement a {@link edu.kit.iti.formal.automation.st.ast.CaseStatement} object.
     * @return a T object.
     */
    T visit(CaseStatement caseStatement);

    //T visit(SymbolicReference symbolicReference);

    /**
     * <p>visit.</p>
     *
     * @param statements a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     * @return a T object.
     */
    T visit(StatementList statements);

    /**
     * <p>visit.</p>
     *
     * @param programDeclaration a {@link edu.kit.iti.formal.automation.st.ast.ProgramDeclaration} object.
     * @return a T object.
     */
    T visit(ProgramDeclaration programDeclaration);

    /**
     * <p>visit.</p>
     *
     * @param tsScalarValue a {@link edu.kit.iti.formal.automation.datatypes.values.ScalarValue} object.
     * @return a T object.
     */
    T visit(ScalarValue<? extends Any, ? extends Object> tsScalarValue);

    /**
     * <p>visit.</p>
     *
     * @param expressions a {@link edu.kit.iti.formal.automation.st.ast.ExpressionList} object.
     * @return a T object.
     */
    T visit(ExpressionList expressions);

    /**
     * <p>visit.</p>
     *
     * @param functionDeclaration a {@link edu.kit.iti.formal.automation.st.ast.FunctionDeclaration} object.
     * @return a T object.
     */
    T visit(FunctionDeclaration functionDeclaration);

    /**
     * <p>visit.</p>
     *
     * @param functionCall a {@link edu.kit.iti.formal.automation.st.ast.FunctionCall} object.
     * @return a T object.
     */
    T visit(FunctionCall functionCall);

    /**
     * <p>visit.</p>
     *
     * @param forStatement a {@link edu.kit.iti.formal.automation.st.ast.ForStatement} object.
     * @return a T object.
     */
    T visit(ForStatement forStatement);

    /**
     * <p>visit.</p>
     *
     * @param resourceDeclaration a {@link edu.kit.iti.formal.automation.st.ast.ResourceDeclaration} object.
     * @return a T object.
     */
    T visit(ResourceDeclaration resourceDeclaration);

    /**
     * <p>visit.</p>
     *
     * @param functionBlockDeclaration a {@link edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration} object.
     * @return a T object.
     */
    T visit(FunctionBlockDeclaration functionBlockDeclaration);

    /**
     * <p>visit.</p>
     *
     * @param returnStatement a {@link edu.kit.iti.formal.automation.st.ast.ReturnStatement} object.
     * @return a T object.
     */
    T visit(ReturnStatement returnStatement);

    /**
     * <p>visit.</p>
     *
     * @param ifStatement a {@link edu.kit.iti.formal.automation.st.ast.IfStatement} object.
     * @return a T object.
     */
    T visit(IfStatement ifStatement);

    /**
     * <p>visit.</p>
     *
     * @param guardedStatement a {@link edu.kit.iti.formal.automation.st.ast.GuardedStatement} object.
     * @return a T object.
     */
    T visit(GuardedStatement guardedStatement);

    /**
     * <p>visit.</p>
     *
     * @param functionBlockCallStatement a {@link FunctionBlockCallStatement} object.
     * @return a T object.
     */
    T visit(FunctionBlockCallStatement functionBlockCallStatement);

    /**
     * <p>visit.</p>
     *
     * @param aCase a {@link edu.kit.iti.formal.automation.st.ast.CaseStatement.Case} object.
     * @return a T object.
     */
    T visit(CaseStatement.Case aCase);

    /**
     * <p>visit.</p>
     *
     * @param stringTypeDeclaration a {@link edu.kit.iti.formal.automation.st.ast.StringTypeDeclaration} object.
     * @return a T object.
     */
    T visit(StringTypeDeclaration stringTypeDeclaration);

    /**
     * <p>visit.</p>
     *
     * @param structureTypeDeclaration a {@link edu.kit.iti.formal.automation.st.ast.StructureTypeDeclaration} object.
     * @return a T object.
     */
    T visit(StructureTypeDeclaration structureTypeDeclaration);

    /**
     * <p>visit.</p>
     *
     * @param subRangeTypeDeclaration a {@link edu.kit.iti.formal.automation.st.ast.SubRangeTypeDeclaration} object.
     * @return a T object.
     */
    T visit(SubRangeTypeDeclaration subRangeTypeDeclaration);

    /**
     * <p>visit.</p>
     *
     * @param simpleTypeDeclaration a {@link edu.kit.iti.formal.automation.st.ast.SimpleTypeDeclaration} object.
     * @return a T object.
     */
    T visit(SimpleTypeDeclaration simpleTypeDeclaration);

    /**
     * <p>visit.</p>
     *
     * @param localScope a {@link edu.kit.iti.formal.automation.scope.LocalScope} object.
     * @return a T object.
     */
    T visit(LocalScope localScope);

    /**
     * <p>visit.</p>
     *
     * @param variableDeclaration a {@link edu.kit.iti.formal.automation.st.ast.VariableDeclaration} object.
     * @return a T object.
     */
    T visit(VariableDeclaration variableDeclaration);

    /**
     * <p>visit.</p>
     *
     * @param commentStatement a {@link edu.kit.iti.formal.automation.st.ast.CommentStatement} object.
     * @return a T object.
     */
    T visit(CommentStatement commentStatement);

    /**
     * <p>visit.</p>
     *
     * @param structureInitialization a {@link edu.kit.iti.formal.automation.st.ast.StructureInitialization} object.
     * @return a T object.
     */
    T visit(StructureInitialization structureInitialization);

    /**
     * <p>visit.</p>
     *
     * @param deref a {@link edu.kit.iti.formal.automation.st.ast.Deref} object.
     * @return a T object.
     */
    T visit(Deref deref);

    /**
     * <p>visit.</p>
     *
     * @param symbolicReference a {@link edu.kit.iti.formal.automation.st.ast.SymbolicReference} object.
     * @return a T object.
     */
    T visit(SymbolicReference symbolicReference);

    /**
     * <p>visit.</p>
     *
     * @param ptd a {@link edu.kit.iti.formal.automation.st.ast.PointerTypeDeclaration} object.
     * @return a T object.
     */
    T visit(PointerTypeDeclaration ptd);

    /**
     * <p>visit.</p>
     *
     * @param init a {@link edu.kit.iti.formal.automation.st.ast.IdentifierInitializer} object.
     * @return a T object.
     */
    T visit(IdentifierInitializer init);


    T visit(ClassDeclaration clazz);

    T visit(MethodDeclaration method);
}
