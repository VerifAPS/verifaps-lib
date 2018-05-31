package edu.kit.iti.formal.automation.visitors


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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.values.ReferenceValue
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.sfclang.ast.*
import edu.kit.iti.formal.automation.st.ast.*

/**
 * Created by weigla on 14.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
interface Visitor<T> {
    /**
     *
     * accept.
     *
     * @param location a [edu.kit.iti.formal.automation.st.ast.Location] object.
     * @return a T object.
     */
    fun visit(location: Location): T

    /**
     *
     * accept.
     *
     * @param initializations a [edu.kit.iti.formal.automation.st.ast.ArrayInitialization] object.
     * @return a T object.
     */
    fun visit(initializations: ArrayInitialization): T

    /**
     *
     * accept.
     *
     * @param arrayTypeDeclaration a [edu.kit.iti.formal.automation.st.ast.ArrayTypeDeclaration] object.
     * @return a T object.
     */
    fun visit(arrayTypeDeclaration: ArrayTypeDeclaration): T

    /**
     *
     * accept.
     *
     * @param assignmentStatement a [edu.kit.iti.formal.automation.st.ast.AssignmentStatement] object.
     * @return a T object.
     */
    fun visit(assignmentStatement: AssignmentStatement): T

    /**
     *
     * accept.
     *
     * @param exitStatement a [edu.kit.iti.formal.automation.st.ast.ExitStatement] object.
     * @return a T object.
     */
    fun visit(exitStatement: ExitStatement): T

    /**
     *
     * accept.
     *
     * @param range a [CaseCondition.Range] object.
     * @return a T object.
     */
    fun visit(range: CaseCondition.Range): T

    /**
     *
     * accept.
     *
     * @param integerCondition a [CaseCondition.IntegerCondition] object.
     * @return a T object.
     */
    fun visit(integerCondition: CaseCondition.IntegerCondition): T

    /**
     *
     * accept.
     *
     * @param enumeration a [CaseCondition.Enumeration] object.
     * @return a T object.
     */
    fun visit(enumeration: CaseCondition.Enumeration): T

    /**
     *
     * accept.
     *
     * @param binaryExpression a [edu.kit.iti.formal.automation.st.ast.BinaryExpression] object.
     * @return a T object.
     */
    fun visit(binaryExpression: BinaryExpression): T

    /**
     *
     * accept.
     *
     * @param configurationDeclaration a [edu.kit.iti.formal.automation.st.ast.ConfigurationDeclaration] object.
     * @return a T object.
     */
    fun visit(configurationDeclaration: ConfigurationDeclaration): T

    //T accept(DirectVariable directVariable);

    /**
     *
     * accept.
     *
     * @param enumerationTypeDeclaration a [edu.kit.iti.formal.automation.st.ast.EnumerationTypeDeclaration] object.
     * @return a T object.
     */
    fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration): T

    /**
     *
     * accept.
     *
     * @param repeatStatement a [edu.kit.iti.formal.automation.st.ast.RepeatStatement] object.
     * @return a T object.
     */
    fun visit(repeatStatement: RepeatStatement): T

    /**
     *
     * accept.
     *
     * @param whileStatement a [edu.kit.iti.formal.automation.st.ast.WhileStatement] object.
     * @return a T object.
     */
    fun visit(whileStatement: WhileStatement): T

    /**
     *
     * accept.
     *
     * @param unaryExpression a [edu.kit.iti.formal.automation.st.ast.UnaryExpression] object.
     * @return a T object.
     */
    fun visit(unaryExpression: UnaryExpression): T

    /**
     *
     * accept.
     *
     * @param typeDeclarations a [edu.kit.iti.formal.automation.st.ast.TypeDeclarations] object.
     * @return a T object.
     */
    fun visit(typeDeclarations: TypeDeclarations): T

    /**
     *
     * accept.
     *
     * @param caseStatement a [edu.kit.iti.formal.automation.st.ast.CaseStatement] object.
     * @return a T object.
     */
    fun visit(caseStatement: CaseStatement): T

    //T accept(SymbolicReference symbolicReference);

    /**
     *
     * accept.
     *
     * @param statements a [edu.kit.iti.formal.automation.st.ast.StatementList] object.
     * @return a T object.
     */
    fun visit(statements: StatementList): T

    /**
     *
     * accept.
     *
     * @param programDeclaration a [edu.kit.iti.formal.automation.st.ast.ProgramDeclaration] object.
     * @return a T object.
     */
    fun visit(programDeclaration: ProgramDeclaration): T


    /**
     *
     * accept.
     *
     * @param expressions a [edu.kit.iti.formal.automation.st.ast.ExpressionList] object.
     * @return a T object.
     */
    fun visit(expressions: ExpressionList): T

    /**
     *
     * accept.
     *
     * @param functionDeclaration a [edu.kit.iti.formal.automation.st.ast.FunctionDeclaration] object.
     * @return a T object.
     */
    fun visit(functionDeclaration: FunctionDeclaration): T

    /**
     *
     * accept.
     *
     * @param invocation a [Invocation] object.
     * @return a T object.
     */
    fun visit(invocation: Invocation): T

    /**
     *
     * accept.
     *
     * @param forStatement a [edu.kit.iti.formal.automation.st.ast.ForStatement] object.
     * @return a T object.
     */
    fun visit(forStatement: ForStatement): T

    /**
     *
     * accept.
     *
     * @param resourceDeclaration a [edu.kit.iti.formal.automation.st.ast.ResourceDeclaration] object.
     * @return a T object.
     */
    fun visit(resourceDeclaration: ResourceDeclaration): T

    /**
     *
     * accept.
     *
     * @param functionBlockDeclaration a [edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration] object.
     * @return a T object.
     */
    fun visit(functionBlockDeclaration: FunctionBlockDeclaration): T

    /**
     *
     * accept.
     *
     * @param returnStatement a [edu.kit.iti.formal.automation.st.ast.ReturnStatement] object.
     * @return a T object.
     */
    fun visit(returnStatement: ReturnStatement): T

    /**
     *
     * accept.
     *
     * @param ifStatement a [edu.kit.iti.formal.automation.st.ast.IfStatement] object.
     * @return a T object.
     */
    fun visit(ifStatement: IfStatement): T

    /**
     *
     * accept.
     *
     * @param guardedStatement a [edu.kit.iti.formal.automation.st.ast.GuardedStatement] object.
     * @return a T object.
     */
    fun visit(guardedStatement: GuardedStatement): T

    /**
     *
     * accept.
     *
     * @param aCase a [edu.kit.iti.formal.automation.st.ast.CaseStatement.Case] object.
     * @return a T object.
     */
    fun visit(aCase: Case): T

    /**
     *
     * accept.
     *
     * @param stringTypeDeclaration a [edu.kit.iti.formal.automation.st.ast.StringTypeDeclaration] object.
     * @return a T object.
     */
    fun visit(stringTypeDeclaration: StringTypeDeclaration): T

    /**
     *
     * accept.
     *
     * @param structureTypeDeclaration a [edu.kit.iti.formal.automation.st.ast.StructureTypeDeclaration] object.
     * @return a T object.
     */
    fun visit(structureTypeDeclaration: StructureTypeDeclaration): T

    /**
     *
     * accept.
     *
     * @param subRangeTypeDeclaration a [edu.kit.iti.formal.automation.st.ast.SubRangeTypeDeclaration] object.
     * @return a T object.
     */
    fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration): T

    /**
     *
     * accept.
     *
     * @param simpleTypeDeclaration a [edu.kit.iti.formal.automation.st.ast.SimpleTypeDeclaration] object.
     * @return a T object.
     */
    fun visit(simpleTypeDeclaration: SimpleTypeDeclaration): T

    /**
     *
     * accept.
     *
     * @param localScope a [edu.kit.iti.formal.automation.scope.Scope] object.
     * @return a T object.
     */
    fun visit(localScope: Scope): T

    /**
     *
     * accept.
     *
     * @param variableDeclaration a [edu.kit.iti.formal.automation.st.ast.VariableDeclaration] object.
     * @return a T object.
     */
    fun visit(variableDeclaration: VariableDeclaration): T

    /**
     *
     * accept.
     *
     * @param commentStatement a [edu.kit.iti.formal.automation.st.ast.CommentStatement] object.
     * @return a T object.
     */
    fun visit(commentStatement: CommentStatement): T

    /**
     *
     * accept.
     *
     * @param structureInitialization a [edu.kit.iti.formal.automation.st.ast.StructureInitialization] object.
     * @return a T object.
     */
    fun visit(structureInitialization: StructureInitialization): T

    /**
     *
     * accept.
     *
     * @param deref a [edu.kit.iti.formal.automation.st.ast.Deref] object.
     * @return a T object.
     */
    fun visit(deref: Deref): T

    /**
     *
     * accept.
     *
     * @param symbolicReference a [edu.kit.iti.formal.automation.st.ast.SymbolicReference] object.
     * @return a T object.
     */
    fun visit(symbolicReference: SymbolicReference): T

    /**
     *
     * accept.
     *
     * @param ptd a [edu.kit.iti.formal.automation.st.ast.PointerTypeDeclaration] object.
     * @return a T object.
     */
    fun visit(ptd: PointerTypeDeclaration): T

    /**
     *
     * accept.
     *
     * @param init a [edu.kit.iti.formal.automation.st.ast.IdentifierInitializer] object.
     * @return a T object.
     */
    fun visit(init: IdentifierInitializer): T

    fun visit(interfaceDeclaration: InterfaceDeclaration): T

    fun visit(clazz: ClassDeclaration): T

    fun visit(method: MethodDeclaration): T

    fun visit(literal: Literal): T

    fun visit(parameter: InvocationParameter): T

    fun visit(referenceSpecification: ReferenceSpecification): T

    fun visit(referenceValue: ReferenceValue): T

    fun visit(globalVariableListDeclaration: GlobalVariableListDeclaration): T

    fun visit(sfcStep: SFCStep): T

    fun visit(actionDeclaration: ActionDeclaration): T

    fun visit(sfcNetwork: SFCNetwork): T

    fun visit(sfc: SFCImplementation): T

    fun visit(transition: SFCTransition): T

    fun visit(invocation: InvocationStatement): T

    fun visit(elements: TopLevelElements): T
    fun visit(empty: EMPTY_EXPRESSION): T {
        TODO("not implemented")
    }
}
