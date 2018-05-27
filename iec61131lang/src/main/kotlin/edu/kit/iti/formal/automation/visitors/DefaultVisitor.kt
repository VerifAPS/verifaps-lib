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
 * Created by weigl on 21.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
open class DefaultVisitor<T> : Visitor<T> {

    /**
     *
     * defaultVisit.
     *
     * @param visitable a [edu.kit.iti.formal.automation.visitors.Visitable] object.
     * @return a T object.
     */
    open fun defaultVisit(visitable: Visitable): T? {
        //return visitable.accept(this);
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(location: Location): T? {
        return defaultVisit(location)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(initializations: ArrayInitialization): T? {
        return defaultVisit(initializations)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration): T? {
        return defaultVisit(arrayTypeDeclaration)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(assignmentStatement: AssignmentStatement): T? {
        return defaultVisit(assignmentStatement)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(exitStatement: ExitStatement): T? {
        return defaultVisit(exitStatement)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(range: CaseCondition.Range): T? {
        return defaultVisit(range)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(integerCondition: CaseCondition.IntegerCondition): T? {
        return defaultVisit(integerCondition)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(enumeration: CaseCondition.Enumeration): T? {
        return defaultVisit(enumeration)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(binaryExpression: BinaryExpression): T? {
        return defaultVisit(binaryExpression)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(configurationDeclaration: ConfigurationDeclaration): T? {
        return defaultVisit(configurationDeclaration)
    }


    /**
     * {@inheritDoc}
     */
    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration): T? {
        return defaultVisit(enumerationTypeDeclaration)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(repeatStatement: RepeatStatement): T? {
        return defaultVisit(repeatStatement)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(whileStatement: WhileStatement): T? {
        return defaultVisit(whileStatement)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(unaryExpression: UnaryExpression): T? {
        return defaultVisit(unaryExpression)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(typeDeclarations: TypeDeclarations): T? {
        return defaultVisit(typeDeclarations)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(caseStatement: CaseStatement): T? {
        return defaultVisit(caseStatement)
    }


    /**
     * {@inheritDoc}
     */
    override fun visit(statements: StatementList): T? {
        return defaultVisit(statements)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(programDeclaration: ProgramDeclaration): T? {
        return defaultVisit(programDeclaration)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(expressions: ExpressionList): T? {
        return defaultVisit(expressions)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(functionDeclaration: FunctionDeclaration): T? {
        return defaultVisit(functionDeclaration)
    }

    override fun visit(invocation: Invocation): T? {
        return defaultVisit(invocation)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(forStatement: ForStatement): T? {
        return defaultVisit(forStatement)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(resourceDeclaration: ResourceDeclaration): T? {
        return defaultVisit(resourceDeclaration)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration): T? {
        return defaultVisit(functionBlockDeclaration)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(returnStatement: ReturnStatement): T? {
        return defaultVisit(returnStatement)
    }


    /**
     * {@inheritDoc}
     */
    override fun visit(ifStatement: IfStatement): T? {
        return defaultVisit(ifStatement)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(guardedStatement: GuardedStatement): T? {
        return defaultVisit(guardedStatement)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(aCase: CaseStatement.Case): T? {
        return defaultVisit(aCase)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(stringTypeDeclaration: StringTypeDeclaration): T? {
        return defaultVisit(stringTypeDeclaration)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(structureTypeDeclaration: StructureTypeDeclaration): T? {
        return defaultVisit(structureTypeDeclaration)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration): T? {
        return defaultVisit(subRangeTypeDeclaration)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration<*>): T? {
        return defaultVisit(simpleTypeDeclaration)
    }

    override fun visit(localScope: Scope): T? {
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(variableDeclaration: VariableDeclaration): T? {
        return defaultVisit(variableDeclaration)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(commentStatement: CommentStatement): T? {
        return defaultVisit(commentStatement)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(structureInitialization: StructureInitialization): T? {
        return defaultVisit(structureInitialization)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(deref: Deref): T? {
        return defaultVisit(deref)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(symbolicReference: SymbolicReference): T? {
        return defaultVisit(symbolicReference)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(ptd: PointerTypeDeclaration): T? {
        return defaultVisit(ptd)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(init: IdentifierInitializer): T? {
        return defaultVisit(init)
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration): T? {
        return defaultVisit(interfaceDeclaration)
    }

    override fun visit(clazz: ClassDeclaration): T? {
        return defaultVisit(clazz)
    }

    override fun visit(method: MethodDeclaration): T? {
        return defaultVisit(method)
    }

    override fun visit(literal: Literal): T? {
        return defaultVisit(literal)
    }

    override fun visit(sfcStep: SFCStep): T? {
        return defaultVisit(sfcStep)
    }

    override fun visit(actionDeclaration: ActionDeclaration): T? {
        return defaultVisit(actionDeclaration)
    }

    override fun visit(sfcNetwork: SFCNetwork): T? {
        return defaultVisit(sfcNetwork)
    }

    override fun visit(sfc: SFCImplementation): T? {
        return defaultVisit(sfc)
    }

    override fun visit(transition: SFCTransition): T? {
        return defaultVisit(transition)
    }

    override fun visit(invocation: InvocationStatement): T? {
        return defaultVisit(invocation)
    }

    override fun visit(parameter: Invocation.Parameter): T? {
        return defaultVisit(parameter)
    }

    override fun visit(referenceSpecification: ReferenceSpecification): T? {
        return defaultVisit(referenceSpecification)
    }

    override fun visit(referenceValue: ReferenceValue): T? {
        return defaultVisit(referenceValue)
    }

    override fun visit(globalVariableListDeclaration: GlobalVariableListDeclaration): T? {
        return defaultVisit(globalVariableListDeclaration)
    }
}
