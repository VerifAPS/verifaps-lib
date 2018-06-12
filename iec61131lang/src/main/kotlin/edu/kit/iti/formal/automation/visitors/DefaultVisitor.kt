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
import edu.kit.iti.formal.automation.st.ast.*

/**
 * Created by weigl on 21.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
open class DefaultVisitor<T>() : DefaultVisitorNN<T?>() {
    override fun defaultVisit(obj: Any?): T? = null
}

abstract class DefaultVisitorNN<T> : Visitor<T> {
    abstract fun defaultVisit(obj: Any?): T

    override fun visit(elements: TopLevelElements): T = defaultVisit(elements)
    override fun visit(location: Location): T = defaultVisit(location)
    override fun visit(initializations: ArrayInitialization): T = defaultVisit(initializations)
    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration): T = defaultVisit(arrayTypeDeclaration)
    override fun visit(assignmentStatement: AssignmentStatement): T = defaultVisit(assignmentStatement)
    override fun visit(exitStatement: ExitStatement): T = defaultVisit(exitStatement)
    override fun visit(range: CaseCondition.Range): T = defaultVisit(range)
    override fun visit(integerCondition: CaseCondition.IntegerCondition): T = defaultVisit(integerCondition)
    override fun visit(enumeration: CaseCondition.Enumeration): T = defaultVisit(enumeration)
    override fun visit(binaryExpression: BinaryExpression): T = defaultVisit(binaryExpression)
    override fun visit(configurationDeclaration: ConfigurationDeclaration): T = defaultVisit(configurationDeclaration)
    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration): T = defaultVisit(enumerationTypeDeclaration)
    override fun visit(repeatStatement: RepeatStatement): T = defaultVisit(repeatStatement)
    override fun visit(whileStatement: WhileStatement): T = defaultVisit(whileStatement)
    override fun visit(unaryExpression: UnaryExpression): T = defaultVisit(unaryExpression)
    override fun visit(typeDeclarations: TypeDeclarations): T = defaultVisit(typeDeclarations)
    override fun visit(caseStatement: CaseStatement): T = defaultVisit(caseStatement)
    override fun visit(statements: StatementList): T = defaultVisit(statements)
    override fun visit(programDeclaration: ProgramDeclaration): T = defaultVisit(programDeclaration)
    override fun visit(expressions: ExpressionList): T = defaultVisit(expressions)
    override fun visit(functionDeclaration: FunctionDeclaration): T = defaultVisit(functionDeclaration)
    override fun visit(invocation: Invocation): T = defaultVisit(invocation)
    override fun visit(forStatement: ForStatement): T = defaultVisit(forStatement)
    override fun visit(resourceDeclaration: ResourceDeclaration): T = defaultVisit(resourceDeclaration)
    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration): T = defaultVisit(functionBlockDeclaration)
    override fun visit(returnStatement: ReturnStatement): T = defaultVisit(returnStatement)
    override fun visit(ifStatement: IfStatement): T = defaultVisit(ifStatement)
    override fun visit(guardedStatement: GuardedStatement): T = defaultVisit(guardedStatement)
    override fun visit(aCase: Case): T = defaultVisit(aCase)
    override fun visit(stringTypeDeclaration: StringTypeDeclaration): T = defaultVisit(stringTypeDeclaration)
    override fun visit(structureTypeDeclaration: StructureTypeDeclaration): T = defaultVisit(structureTypeDeclaration)
    override fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration): T = defaultVisit(subRangeTypeDeclaration)
    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration): T = defaultVisit(simpleTypeDeclaration)
    override fun visit(localScope: Scope): T = defaultVisit(localScope)
    override fun visit(variableDeclaration: VariableDeclaration): T = defaultVisit(variableDeclaration)
    override fun visit(commentStatement: CommentStatement): T = defaultVisit(commentStatement)
    override fun visit(structureInitialization: StructureInitialization): T = defaultVisit(structureInitialization)
    override fun visit(deref: Deref): T = defaultVisit(deref)
    override fun visit(symbolicReference: SymbolicReference): T = defaultVisit(symbolicReference)
    override fun visit(ptd: PointerTypeDeclaration): T = defaultVisit(ptd)
    override fun visit(init: IdentifierInitializer): T = defaultVisit(init)
    override fun visit(interfaceDeclaration: InterfaceDeclaration): T = defaultVisit(interfaceDeclaration)
    override fun visit(clazz: ClassDeclaration): T = defaultVisit(clazz)
    override fun visit(method: MethodDeclaration): T = defaultVisit(method)
    override fun visit(literal: Literal): T = defaultVisit(literal)
    override fun visit(sfcStep: SFCStep): T = defaultVisit(sfcStep)
    override fun visit(actionDeclaration: ActionDeclaration): T = defaultVisit(actionDeclaration)
    override fun visit(sfcNetwork: SFCNetwork): T = defaultVisit(sfcNetwork)
    override fun visit(sfc: SFCImplementation): T = defaultVisit(sfc)
    override fun visit(transition: SFCTransition): T = defaultVisit(transition)
    override fun visit(invocation: InvocationStatement): T = defaultVisit(invocation)
    override fun visit(parameter: InvocationParameter): T = defaultVisit(parameter)
    override fun visit(referenceSpecification: ReferenceTypeDeclaration): T = defaultVisit(referenceSpecification)
    override fun visit(referenceValue: ReferenceValue): T = defaultVisit(referenceValue)
    override fun visit(globalVariableListDeclaration: GlobalVariableListDeclaration): T = defaultVisit(globalVariableListDeclaration)
    override fun visit(empty: EMPTY_EXPRESSION) = defaultVisit(empty)
}