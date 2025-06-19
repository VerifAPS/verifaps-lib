/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.automation.visitors

import edu.kit.iti.formal.automation.datatypes.values.ReferenceValue
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import java.lang.IllegalStateException

interface Visitor<T> {
    fun visit(location: Location): T
    fun visit(initializations: ArrayInitialization): T
    fun visit(arrayTypeDeclaration: ArrayTypeDeclaration): T
    fun visit(assignmentStatement: AssignmentStatement): T
    fun visit(exitStatement: ExitStatement): T
    fun visit(range: CaseCondition.Range): T
    fun visit(integerCondition: CaseCondition.IntegerCondition): T
    fun visit(enumeration: CaseCondition.Enumeration): T
    fun visit(binaryExpression: BinaryExpression): T
    fun visit(configurationDeclaration: ConfigurationDeclaration): T

    // T accept(DirectVariable directVariable);
    fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration): T

    fun visit(repeatStatement: RepeatStatement): T
    fun visit(whileStatement: WhileStatement): T
    fun visit(unaryExpression: UnaryExpression): T
    fun visit(typeDeclarations: TypeDeclarations): T
    fun visit(caseStatement: CaseStatement): T

    // T accept(SymbolicReference symbolicReference);
    fun visit(statements: StatementList): T

    fun visit(programDeclaration: ProgramDeclaration): T
    fun visit(expressions: ExpressionList): T
    fun visit(functionDeclaration: FunctionDeclaration): T
    fun visit(invocation: Invocation): T
    fun visit(forStatement: ForStatement): T
    fun visit(resourceDeclaration: ResourceDeclaration): T
    fun visit(functionBlockDeclaration: FunctionBlockDeclaration): T
    fun visit(returnStatement: ReturnStatement): T
    fun visit(ifStatement: IfStatement): T
    fun visit(guardedStatement: GuardedStatement): T
    fun visit(aCase: Case): T
    fun visit(stringTypeDeclaration: StringTypeDeclaration): T
    fun visit(structureTypeDeclaration: StructureTypeDeclaration): T
    fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration): T
    fun visit(simpleTypeDeclaration: SimpleTypeDeclaration): T
    fun visit(localScope: Scope): T
    fun visit(variableDeclaration: VariableDeclaration): T
    fun visit(commentStatement: CommentStatement): T
    fun visit(structureInitialization: StructureInitialization): T
    fun visit(deref: Deref): T
    fun visit(symbolicReference: SymbolicReference): T
    fun visit(ptd: PointerTypeDeclaration): T
    fun visit(init: IdentifierInitializer): T
    fun visit(interfaceDeclaration: InterfaceDeclaration): T
    fun visit(clazz: ClassDeclaration): T
    fun visit(method: MethodDeclaration): T
    fun visit(literal: Literal): T
    fun visit(parameter: InvocationParameter): T
    fun visit(referenceSpecification: ReferenceTypeDeclaration): T
    fun visit(referenceValue: ReferenceValue): T
    fun visit(globalVariableListDeclaration: GlobalVariableListDeclaration): T
    fun visit(sfcStep: SFCStep): T
    fun visit(actionDeclaration: ActionDeclaration): T
    fun visit(sfcNetwork: SFCNetwork): T
    fun visit(sfc: SFCImplementation): T
    fun visit(transition: SFCTransition): T
    fun visit(invocation: InvocationStatement): T
    fun visit(elements: PouElements): T
    fun visit(empty: EMPTY_EXPRESSION): T = throw IllegalStateException()

    fun visit(jump: JumpStatement): T
    fun visit(label: LabelStatement): T
    fun visit(namespace: NamespaceDeclaration): T
    fun visit(blockStatement: BlockStatement): T
    fun visit(special: SpecialStatement): T
}