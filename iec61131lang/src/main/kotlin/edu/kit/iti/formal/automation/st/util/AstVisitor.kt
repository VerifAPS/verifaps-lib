package edu.kit.iti.formal.automation.st.util

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.values.ReferenceValue
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitorNN
import edu.kit.iti.formal.automation.visitors.Visitable
import edu.kit.iti.formal.automation.visitors.Visitor
import java.util.*
import kotlin.collections.ArrayList

interface ITraversal<T> {
    val visitor: Visitor<T>
    fun traverse(assignmentStatement: AssignmentStatement)
    fun traverse(range: CaseCondition.Range)
    fun traverse(integerCondition: CaseCondition.IntegerCondition)
    fun traverse(enumeration: CaseCondition.Enumeration)
    fun traverse(binaryExpression: BinaryExpression)
    fun traverse(repeatStatement: RepeatStatement)
    fun traverse(whileStatement: WhileStatement)
    fun traverse(unaryExpression: UnaryExpression)
    fun traverse(typeDeclarations: TypeDeclarations)
    fun traverse(caseStatement: CaseStatement)
    fun traverse(statements: StatementList)
    fun traverse(programDeclaration: ProgramDeclaration)
    fun traverse(expressions: ExpressionList)
    fun traverse(functionDeclaration: FunctionDeclaration)
    fun traverse(forStatement: ForStatement)
    fun traverse(functionBlockDeclaration: FunctionBlockDeclaration)
    /**
     * {@inheritDoc}
     */
    fun traverse(ifStatement: IfStatement)

    /**
     * {@inheritDoc}
     */
    fun traverse(guardedStatement: GuardedStatement)

    /**
     * {@inheritDoc}
     */
    fun traverse(aCase: Case)

    /**
     * {@inheritDoc}
     */
    fun traverse(localScope: Scope)

    /**
     * {@inheritDoc}
     */
    fun traverse(variableDeclaration: VariableDeclaration)

    fun traverse(arrayinit: ArrayInitialization)
    /**
     * {@inheritDoc}
     */
    fun traverse(invocation: Invocation)

    fun traverse(parameter: InvocationParameter)
    fun traverse(invocation: InvocationStatement)
    fun traverse(stringTypeDeclaration: StringTypeDeclaration)
    fun traverse(structureInitialization: StructureInitialization)
    fun traverse(clazz: ClassDeclaration)
    fun traverse(interfaceDeclaration: InterfaceDeclaration)
    fun traverse(method: MethodDeclaration)
    fun traverse(globalVariableListDeclaration: GlobalVariableListDeclaration)
    fun traverse(referenceValue: ReferenceValue)
    fun traverse(location: Location)
    fun traverse(arrayTypeDeclaration: ArrayTypeDeclaration)
    fun traverse(exitStatement: ExitStatement)
    fun traverse(configurationDeclaration: ConfigurationDeclaration)
    fun traverse(enumerationTypeDeclaration: EnumerationTypeDeclaration)
    fun traverse(resourceDeclaration: ResourceDeclaration)
    fun traverse(returnStatement: ReturnStatement)
    fun traverse(structureTypeDeclaration: StructureTypeDeclaration)
    fun traverse(subRangeTypeDeclaration: SubRangeTypeDeclaration)
    fun traverse(simpleTypeDeclaration: SimpleTypeDeclaration)
    fun traverse(commentStatement: CommentStatement)
    fun traverse(deref: Deref)
    fun traverse(symbolicReference: SymbolicReference)
    fun traverse(ptd: PointerTypeDeclaration)
    fun traverse(init: IdentifierInitializer)
    fun traverse(literal: Literal)
    fun traverse(referenceSpecification: ReferenceTypeDeclaration)
    fun traverse(sfcStep: SFCStep)
    fun traverse(actionDeclaration: ActionDeclaration)
    fun traverse(sfcNetwork: SFCNetwork)
    fun traverse(sfc: SFCImplementation)
    fun traverse(transition: SFCTransition)
    fun traverse(elements: PouElements)
    fun traverse(empty: EMPTY_EXPRESSION)
}

/**
 * Created by weigl on 10/07/14.
 *
 * @author weigl
 * @version $Id: $Id
 */

/**
 *
 */
open class ImmutableTraversal<T>(override var visitor: Visitor<T>) : ITraversal<T> {
    override fun traverse(assignmentStatement: AssignmentStatement) {
        assignmentStatement.expression.accept(visitor)
        assignmentStatement.location.accept(visitor)
    }

    override fun traverse(range: CaseCondition.Range) {
        range.start!!.accept(visitor)
        range.stop!!.accept(visitor)
    }

    override fun traverse(integerCondition: CaseCondition.IntegerCondition) {
        integerCondition.value.accept(visitor)
    }

    override fun traverse(enumeration: CaseCondition.Enumeration) {
        enumeration.start.accept(visitor)
        enumeration.stop!!.accept(visitor)
    }

    override fun traverse(binaryExpression: BinaryExpression) {
        binaryExpression.leftExpr.accept(visitor)
        binaryExpression.rightExpr.accept(visitor)
    }

    override fun traverse(repeatStatement: RepeatStatement) {
        repeatStatement.condition.accept(visitor)
        repeatStatement.statements.accept(visitor)
    }

    override fun traverse(whileStatement: WhileStatement) {
        whileStatement.condition.accept(visitor)
        whileStatement.statements.accept(visitor)
    }

    override fun traverse(unaryExpression: UnaryExpression) {
        unaryExpression.expression.accept(visitor)
    }

    override fun traverse(typeDeclarations: TypeDeclarations) {
        for (td in typeDeclarations)
            td.accept(visitor)
    }

    override fun traverse(caseStatement: CaseStatement) {
        caseStatement.expression.accept(visitor)
        for (c in caseStatement.cases)
            c.accept(visitor)

        caseStatement.elseCase!!.accept(visitor)
    }

    override fun traverse(statements: StatementList) {
        for (s in statements)
            s.accept(visitor)
    }

    override fun traverse(programDeclaration: ProgramDeclaration) {
        programDeclaration.scope.accept(visitor)
        programDeclaration.stBody!!.accept(visitor)
    }

    override fun traverse(expressions: ExpressionList) {
        for (e in expressions)
            e.accept(visitor)
    }

    override fun traverse(functionDeclaration: FunctionDeclaration) {
        functionDeclaration.scope.accept(visitor)
        functionDeclaration.stBody?.accept(visitor)
    }

    override fun traverse(forStatement: ForStatement) {
        forStatement.start.accept(visitor)
        forStatement.step?.accept(visitor)
        forStatement.stop.accept(visitor)
        forStatement.statements.accept(visitor)
    }

    override fun traverse(functionBlockDeclaration: FunctionBlockDeclaration) {
        //currentFullScope = OOUtils.getEffectiveScope(functionBlockDeclaration);
        functionBlockDeclaration.scope.accept(visitor)
        functionBlockDeclaration.actions.forEach { it.accept(visitor) }
        functionBlockDeclaration.methods.forEach { it.accept(visitor) }
        if (functionBlockDeclaration.stBody != null)
            functionBlockDeclaration.stBody!!.accept(visitor)
        if (functionBlockDeclaration.sfcBody != null)
            functionBlockDeclaration.sfcBody!!.accept(visitor)
    }


    /**
     * {@inheritDoc}
     */
    override fun traverse(ifStatement: IfStatement) {
        for (gs in ifStatement.conditionalBranches)
            gs.accept(visitor)

        ifStatement.elseBranch.accept(visitor)
    }

    /**
     * {@inheritDoc}
     */
    override fun traverse(guardedStatement: GuardedStatement) {
        guardedStatement.condition.accept(visitor)
        guardedStatement.statements.accept(visitor)
    }

    /**
     * {@inheritDoc}
     */
    override fun traverse(aCase: Case) {
        aCase.statements.accept(visitor)
        for (c in aCase.conditions)
            c.accept(visitor)
    }

    /**
     * {@inheritDoc}
     */
    override fun traverse(localScope: Scope) {
        for (vd in localScope)
            vd.accept(visitor)
    }

    /**
     * {@inheritDoc}
     */
    override fun traverse(variableDeclaration: VariableDeclaration) {
        if (null != variableDeclaration.typeDeclaration) {
            variableDeclaration.typeDeclaration!!.accept(visitor)
        }
    }

    override fun traverse(arrayinit: ArrayInitialization) {
        for (init in arrayinit.initValues)
            init.accept(visitor)
    }

    /**
     * {@inheritDoc}
     */
    override fun traverse(invocation: Invocation) {
        invocation.callee.accept(visitor)
        invocation.parameters.forEach { e -> e.accept(visitor) }
    }

    override fun traverse(parameter: InvocationParameter) {
        parameter.expression.accept(visitor)
    }

    override fun traverse(invocation: InvocationStatement) {
        invocation.callee.accept(visitor)
        invocation.parameters.forEach { it.accept(visitor) }
    }

    override fun traverse(stringTypeDeclaration: StringTypeDeclaration) {
        if (stringTypeDeclaration.initialization != null)
            stringTypeDeclaration.initialization!!.accept(visitor)
    }

    override fun traverse(structureInitialization: StructureInitialization) {
        structureInitialization.initValues
                .values.forEach { v -> v.accept(visitor) }
    }

    override fun traverse(clazz: ClassDeclaration) {
        clazz.scope.accept(visitor)
        for (m in ArrayList(clazz.methods)) {
            m.accept(visitor)
        }
    }

    override fun traverse(interfaceDeclaration: InterfaceDeclaration) {
        //TODO inferface? interfaceDeclaration.scope.accept(visitor)
        for (m in interfaceDeclaration.methods)
            m.accept(visitor)
    }

    override fun traverse(method: MethodDeclaration) {
        method.scope.accept(visitor)
        method.stBody?.accept(visitor)
    }

    override fun traverse(globalVariableListDeclaration: GlobalVariableListDeclaration) {
        globalVariableListDeclaration.scope.accept(visitor)
    }

    override fun traverse(referenceValue: ReferenceValue) {
        referenceValue.referenceTo.accept(visitor)
    }

    override fun traverse(location: Location) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun traverse(arrayTypeDeclaration: ArrayTypeDeclaration) {}

    override fun traverse(exitStatement: ExitStatement) {}

    override fun traverse(configurationDeclaration: ConfigurationDeclaration) {}

    override fun traverse(enumerationTypeDeclaration: EnumerationTypeDeclaration) {}

    override fun traverse(resourceDeclaration: ResourceDeclaration) {}

    override fun traverse(returnStatement: ReturnStatement) {}

    override fun traverse(structureTypeDeclaration: StructureTypeDeclaration) {
        structureTypeDeclaration.fields.forEach { it.init?.accept(visitor) }
    }

    override fun traverse(subRangeTypeDeclaration: SubRangeTypeDeclaration) {}

    override fun traverse(simpleTypeDeclaration: SimpleTypeDeclaration) {
        simpleTypeDeclaration.initialization?.accept(visitor)
    }

    override fun traverse(commentStatement: CommentStatement) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun traverse(deref: Deref) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun traverse(symbolicReference: SymbolicReference) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun traverse(ptd: PointerTypeDeclaration) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun traverse(init: IdentifierInitializer) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun traverse(literal: Literal) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun traverse(referenceSpecification: ReferenceTypeDeclaration) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun traverse(sfcStep: SFCStep) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun traverse(actionDeclaration: ActionDeclaration) {
        actionDeclaration.sfcBody?.accept(visitor)
        actionDeclaration.stBody?.accept(visitor)
    }

    override fun traverse(sfcNetwork: SFCNetwork) {
        sfcNetwork.steps.forEach { it.accept(visitor) }
    }

    override fun traverse(sfc: SFCImplementation) {
        sfc.networks.forEach { it.accept(visitor) }
        //sfc.actions.forEach { it.accept(visitor) }
    }

    override fun traverse(transition: SFCTransition) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun traverse(elements: PouElements) {
        visitList(elements)
    }

    fun visitList(elements: Collection<Visitable>) =
            elements.forEach { it.accept(visitor) }

    override fun traverse(empty: EMPTY_EXPRESSION) {}
}

/**
 *
 * AstMutableVisitor class.
 * This visitors defines all function with go down and setting the results of accept as the new value.
 * Not copying datastructures.
 *
 * @author Alexander Weigl (26.06.2014)
 */
class MutableTraversal<T>(override var visitor: Visitor<T>) : ITraversal<T> {
    override fun traverse(elements: PouElements) {
        val newElements = visitList(elements)
        elements.clear()
        elements.addAll(newElements)
    }

    override fun traverse(empty: EMPTY_EXPRESSION) {}

    override fun traverse(assignmentStatement: AssignmentStatement) {
        assignmentStatement.expression = assignmentStatement.expression.accept(visitor) as Expression
        assignmentStatement.location = assignmentStatement.location.accept(visitor) as SymbolicReference
    }


    override fun traverse(integerCondition: CaseCondition.IntegerCondition) {
        val sv = integerCondition.value.accept(visitor) as Literal
        integerCondition.value = sv as IntegerLit
    }


    override fun traverse(enumeration: CaseCondition.Enumeration) {
        enumeration.start = enumeration.start.accept(visitor) as Literal
        enumeration.stop = enumeration.stop!!.accept(visitor) as Literal
    }


    override fun traverse(binaryExpression: BinaryExpression) {
        binaryExpression.leftExpr = binaryExpression.leftExpr.accept(visitor) as Expression
        binaryExpression.rightExpr = binaryExpression.rightExpr.accept(visitor) as Expression
    }


    override fun traverse(unaryExpression: UnaryExpression) {
        unaryExpression.expression = unaryExpression.expression.accept(visitor) as Expression
    }


    override fun traverse(repeatStatement: RepeatStatement) {
        repeatStatement.condition = repeatStatement.condition.accept(visitor) as Expression
        repeatStatement.statements = repeatStatement.statements.accept(visitor) as StatementList
    }


    override fun traverse(whileStatement: WhileStatement) {
        whileStatement.condition = whileStatement.condition.accept(visitor) as Expression
        whileStatement.statements = whileStatement.statements.accept(visitor) as StatementList
    }


    override fun traverse(caseStatement: CaseStatement) {
        val l = LinkedList<Case>()
        for (c in caseStatement.cases) {
            l.add(c.accept(visitor) as Case)
        }

        caseStatement.cases.clear()
        caseStatement.cases.addAll(l)

        caseStatement.expression = caseStatement.expression.accept(visitor) as Expression
        caseStatement.elseCase = caseStatement.elseCase!!.accept(visitor) as StatementList
    }


    /*
    @Override
    public Object accept(SymbolicReference symbolicReference) {

        if (symbolicReference.getSub() != null)
            symbolicReference.setSub((Reference) symbolicReference.getSub().accept(visitor));

        if (symbolicReference.getSubscripts() != null)
            symbolicReference.setSubscripts((ExpressionList)
                    symbolicReference.getSubscripts().accept(visitor));

        return symbolicReference;
    }*/


    override fun traverse(statements: StatementList) {
        val copy = statements.toList()
        statements.clear()
        for (s in copy.toList()) {
            val stmt = s.accept(visitor)
            if (stmt is StatementList) {
                statements.addAll(stmt)
            } else
                statements.add(stmt as Statement)
        }
    }


    override fun traverse(programDeclaration: ProgramDeclaration) {
        programDeclaration.scope = programDeclaration.scope.accept(visitor) as Scope
        programDeclaration.stBody = programDeclaration.stBody!!.accept(visitor) as StatementList
    }


    override fun traverse(invocation: Invocation) {
        invocation.callee = invocation.callee.accept(visitor) as SymbolicReference
        invocation.parameters.setAll(
                invocation.parameters
                        .map { p -> p.accept(visitor) as InvocationParameter }
        )
    }


    override fun traverse(forStatement: ForStatement) {
        forStatement.start = forStatement.start.accept(visitor) as Expression
        forStatement.statements = forStatement.statements.accept(visitor) as StatementList
        if (forStatement.step != null)
            forStatement.step = forStatement.step!!.accept(visitor) as Expression
        forStatement.stop = forStatement.stop.accept(visitor) as Expression
    }


    override fun traverse(ifStatement: IfStatement) {
        ifStatement.conditionalBranches.setAll(visitList(ifStatement.conditionalBranches))
        ifStatement.elseBranch = ifStatement.elseBranch.accept(visitor) as StatementList
    }


    override fun traverse(commentStatement: CommentStatement) {}


    override fun traverse(guardedStatement: GuardedStatement) {
        guardedStatement.condition = guardedStatement.condition.accept(visitor) as Expression
        guardedStatement.statements = guardedStatement.statements.accept(visitor) as StatementList
    }


    override fun traverse(fbc: InvocationStatement) {
        fbc.callee = fbc.callee.accept(visitor) as SymbolicReference
        fbc.parameters = fbc.parameters
                .map { it.accept(visitor) as InvocationParameter }
                .toMutableList()
    }

    override fun traverse(parameter: InvocationParameter) {
        parameter.expression = parameter.expression.accept(visitor) as Expression
    }

    fun <U : Visitable> visitList(seq: MutableCollection<U>): Collection<U> = seq.map { it.accept(visitor) as U }


    override fun traverse(aCase: Case) {
        val v = visitList(aCase.conditions)
        aCase.conditions.setAll(v)
        aCase.statements = aCase.statements.accept(visitor) as StatementList
    }

    override fun traverse(arrayTypeDeclaration: ArrayTypeDeclaration) {}


    override fun traverse(exitStatement: ExitStatement) {
    }


    override fun traverse(range: CaseCondition.Range) {
        range.start = range.start!!.accept(visitor) as Literal
        range.stop = range.stop!!.accept(visitor) as Literal
    }


    override fun traverse(configurationDeclaration: ConfigurationDeclaration) {
    }


    override fun traverse(localScope: Scope) {
        val variables = ArrayList(localScope.variables)
        for (variable in variables) {
            //assert variable.getParent() != null;
            val newVariable = variable.accept(visitor) as VariableDeclaration
            if (newVariable == null)
                localScope.variables.remove(variable.name)
            else
                localScope.variables.replace(variable.name, newVariable)
        }
    }


    override fun traverse(variableDeclaration: VariableDeclaration) {
        variableDeclaration.typeDeclaration = variableDeclaration.typeDeclaration!!.accept(visitor) as TypeDeclaration
    }


    override fun traverse(arrayinit: ArrayInitialization) {
    }


    override fun traverse(enumerationTypeDeclaration: EnumerationTypeDeclaration) {
    }


    override fun traverse(typeDeclarations: TypeDeclarations) {
        val td = TypeDeclarations()
        for (t in typeDeclarations)
            td.add(t.accept(visitor) as TypeDeclaration)
    }


    override fun traverse(expressions: ExpressionList) {
        val expressionList = ExpressionList()
        for (e in expressions)
            expressionList.add(e.accept(visitor) as Expression)
    }


    override fun traverse(functionDeclaration: FunctionDeclaration) {
        functionDeclaration.scope = functionDeclaration.scope.accept(visitor) as Scope
        functionDeclaration.stBody = functionDeclaration.stBody?.accept(visitor) as StatementList
    }


    override fun traverse(resourceDeclaration: ResourceDeclaration) {
    }


    override fun traverse(fbd: FunctionBlockDeclaration) {
        if (fbd.stBody != null)
            fbd.stBody = fbd.stBody!!.accept(visitor) as StatementList
        if (fbd.sfcBody != null)
            fbd.sfcBody = fbd.sfcBody!!.accept(visitor) as SFCImplementation

        val a = visitList(fbd.actions)

    }


    override fun traverse(returnStatement: ReturnStatement) {
    }


    override fun traverse(stringTypeDeclaration: StringTypeDeclaration) {
    }


    override fun traverse(structureTypeDeclaration: StructureTypeDeclaration) {
    }


    override fun traverse(subRangeTypeDeclaration: SubRangeTypeDeclaration) {
    }


    override fun traverse(simpleTypeDeclaration: SimpleTypeDeclaration) {
    }


    override fun traverse(structureInitialization: StructureInitialization) {
    }

    override fun traverse(location: Location) {
    }

    override fun traverse(deref: Deref) {
    }

    override fun traverse(symbolicReference: SymbolicReference) {
        if (symbolicReference.hasSubscripts())
            symbolicReference.subscripts = symbolicReference.subscripts!!.accept(visitor) as ExpressionList
    }

    override fun traverse(referenceValue: ReferenceValue) {
        referenceValue.referenceTo = referenceValue.referenceTo.accept(visitor) as SymbolicReference
    }

    override fun traverse(ptd: PointerTypeDeclaration) {
    }

    override fun traverse(init: IdentifierInitializer) {
    }

    override fun traverse(clazz: ClassDeclaration) {
        clazz.scope = clazz.scope.accept(visitor) as Scope

        val methods = ArrayList<MethodDeclaration>(clazz.methods.size)
        for (method in clazz.methods) {
            val newMethod = method.accept(visitor) as MethodDeclaration
            if (newMethod != null)
                methods.add(newMethod)
        }
        //clazz.setMethods(methods)
    }

    override fun traverse(method: MethodDeclaration) {
        method.scope = method.scope.accept(visitor) as Scope
        method.stBody = method.stBody.accept(visitor) as StatementList
    }

    override fun traverse(interfaceDeclaration: InterfaceDeclaration) {
        val methods = ArrayList<MethodDeclaration>(interfaceDeclaration.methods.size)
        for (method in interfaceDeclaration.methods) {
            val newMethod = method.accept(visitor) as MethodDeclaration
            if (newMethod != null)
                methods.add(method)
        }
        interfaceDeclaration.methods = methods
    }

    override fun traverse(gvlDecl: GlobalVariableListDeclaration) {
        gvlDecl.scope = (gvlDecl.scope.accept(visitor) as Scope?)!!
    }

    override fun traverse(literal: Literal) {}

    override fun traverse(referenceSpecification: ReferenceTypeDeclaration) {}

    override fun traverse(sfcStep: SFCStep) {}

    override fun traverse(actionDeclaration: ActionDeclaration) {}

    override fun traverse(sfcNetwork: SFCNetwork) {}

    override fun traverse(sfc: SFCImplementation) {}

    override fun traverse(transition: SFCTransition) {}
}

fun <E> MutableCollection<E>.setAll(seq: Collection<E>) {
    clear()
    addAll(seq)
}

open class AstTraversal : DefaultVisitorNN<Unit>() {
    override fun defaultVisit(obj: Any) {}
}


abstract class AstVisitor<T> : DefaultVisitorNN<T>() {
    protected var traversalPolicy: ITraversal<T> = ImmutableTraversal(this)

    override fun visit(elements: PouElements): T {
        traversalPolicy.traverse(elements)
        return super.visit(elements)
    }

    override fun visit(assignmentStatement: AssignmentStatement): T {
        traversalPolicy.traverse(assignmentStatement)
        return super.visit(assignmentStatement)
    }

    override fun visit(range: CaseCondition.Range): T {
        traversalPolicy.traverse(range)
        return super<DefaultVisitorNN>.visit(range)
    }

    override fun visit(integerCondition: CaseCondition.IntegerCondition): T {
        traversalPolicy.traverse(integerCondition)
        return super<DefaultVisitorNN>.visit(integerCondition)
    }

    override fun visit(enumeration: CaseCondition.Enumeration): T {
        traversalPolicy.traverse(enumeration)
        return super<DefaultVisitorNN>.visit(enumeration)
    }

    override fun visit(binaryExpression: BinaryExpression): T {
        traversalPolicy.traverse(binaryExpression)
        return super<DefaultVisitorNN>.visit(binaryExpression)
    }

    override fun visit(repeatStatement: RepeatStatement): T {
        traversalPolicy.traverse(repeatStatement)
        return super<DefaultVisitorNN>.visit(repeatStatement)

    }

    override fun visit(whileStatement: WhileStatement): T {
        traversalPolicy.traverse(whileStatement)
        return super<DefaultVisitorNN>.visit(whileStatement)
    }

    override fun visit(unaryExpression: UnaryExpression): T {
        traversalPolicy.traverse(unaryExpression)
        return super<DefaultVisitorNN>.visit(unaryExpression)
    }

    override fun visit(typeDeclarations: TypeDeclarations): T {
        traversalPolicy.traverse(typeDeclarations)
        return super<DefaultVisitorNN>.visit(typeDeclarations)
    }

    override fun visit(caseStatement: CaseStatement): T {
        traversalPolicy.traverse(caseStatement)
        return super<DefaultVisitorNN>.visit(caseStatement)
    }

    override fun visit(statements: StatementList): T {
        traversalPolicy.traverse(statements)
        return super<DefaultVisitorNN>.visit(statements)
    }

    override fun visit(programDeclaration: ProgramDeclaration): T {
        traversalPolicy.traverse(programDeclaration)
        return super<DefaultVisitorNN>.visit(programDeclaration)
    }

    override fun visit(expressions: ExpressionList): T {
        traversalPolicy.traverse(expressions)
        return super<DefaultVisitorNN>.visit(expressions)
    }

    override fun visit(functionDeclaration: FunctionDeclaration): T {
        traversalPolicy.traverse(functionDeclaration)
        return super<DefaultVisitorNN>.visit(functionDeclaration)
    }

    override fun visit(forStatement: ForStatement): T {
        traversalPolicy.traverse(forStatement)
        return super<DefaultVisitorNN>.visit(forStatement)
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration): T {
        traversalPolicy.traverse(functionBlockDeclaration)
        return super<DefaultVisitorNN>.visit(functionBlockDeclaration)
    }


    override fun visit(ifStatement: IfStatement): T {
        traversalPolicy.traverse(ifStatement)
        return super<DefaultVisitorNN>.visit(ifStatement)
    }

    override fun visit(guardedStatement: GuardedStatement): T {
        traversalPolicy.traverse(guardedStatement)
        return super<DefaultVisitorNN>.visit(guardedStatement)
    }

    override fun visit(aCase: Case): T {
        traversalPolicy.traverse(aCase)
        return super<DefaultVisitorNN>.visit(aCase)
    }

    override fun visit(localScope: Scope): T {
        traversalPolicy.traverse(localScope)
        return super<DefaultVisitorNN>.visit(localScope)
    }

    override fun visit(variableDeclaration: VariableDeclaration): T {
        traversalPolicy.traverse(variableDeclaration)
        return super<DefaultVisitorNN>.visit(variableDeclaration)
    }

    override fun visit(arrayinit: ArrayInitialization): T {
        traversalPolicy.traverse(arrayinit)
        return super<DefaultVisitorNN>.visit(arrayinit)
    }

    override fun visit(actionDeclaration: ActionDeclaration): T {
        traversalPolicy.traverse(actionDeclaration)
        return super.visit(actionDeclaration)
    }

    override fun visit(invocation: Invocation): T {
        traversalPolicy.traverse(invocation)
        return super.visit(invocation)
    }

    override fun visit(parameter: InvocationParameter): T {
        traversalPolicy.traverse(parameter)
        return super.visit(parameter)
    }

    override fun visit(invocation: InvocationStatement): T {
        traversalPolicy.traverse(invocation)
        return super.visit(invocation)
    }

    override fun visit(stringTypeDeclaration: StringTypeDeclaration): T {
        traversalPolicy.traverse(stringTypeDeclaration)
        return super.visit(stringTypeDeclaration)
    }

    override fun visit(structureInitialization: StructureInitialization): T {
        traversalPolicy.traverse(structureInitialization)
        return super<DefaultVisitorNN>.visit(structureInitialization)
    }

    override fun visit(clazz: ClassDeclaration): T {
        traversalPolicy.traverse(clazz)
        return super<DefaultVisitorNN>.visit(clazz)
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration): T {
        traversalPolicy.traverse(interfaceDeclaration)
        return super<DefaultVisitorNN>.visit(interfaceDeclaration)

    }

    override fun visit(method: MethodDeclaration): T {
        traversalPolicy.traverse(method)
        return super<DefaultVisitorNN>.visit(method)
    }

    override fun visit(gvlDecl: GlobalVariableListDeclaration): T {
        traversalPolicy.traverse(gvlDecl)
        return super<DefaultVisitorNN>.visit(gvlDecl)
    }

    override fun visit(referenceValue: ReferenceValue): T {
        traversalPolicy.traverse(referenceValue)
        return super<DefaultVisitorNN>.visit(referenceValue)
    }

}

open abstract class AstVisitorWithScope<T> : AstVisitor<T>() {
    protected lateinit var scope: Scope
    override fun visit(localScope: Scope): T {
        scope = localScope
        return super.visit(localScope)
    }
}



/**
 *
 * AstMutableVisitor class.
 * This visitors defines all function with go down and setting the results of accept as the new value.
 * Not copying datastructures.
 *
 * @author Alexander Weigl (26.06.2014), (17.06.2018)
 */
open class AstMutableVisitor : AstVisitor<Any>() {
    init {
        traversalPolicy = MutableTraversal(this)
    }

    override fun defaultVisit(obj: Any): Any = obj

    override fun visit(assignmentStatement: AssignmentStatement): Statement {
        return super.visit(assignmentStatement) as AssignmentStatement
    }

    override fun visit(range: CaseCondition.Range): CaseCondition.Range {
        return super.visit(range) as CaseCondition.Range
    }

    override fun visit(integerCondition: CaseCondition.IntegerCondition): CaseCondition.IntegerCondition {
        return super.visit(integerCondition) as CaseCondition.IntegerCondition
    }

    override fun visit(enumeration: CaseCondition.Enumeration): CaseCondition.Enumeration {
        return super.visit(enumeration) as CaseCondition.Enumeration
    }

    override fun visit(binaryExpression: BinaryExpression): Expression {
        return super.visit(binaryExpression) as BinaryExpression
    }

    override fun visit(repeatStatement: RepeatStatement): RepeatStatement {
        return super.visit(repeatStatement) as RepeatStatement
    }

    override fun visit(whileStatement: WhileStatement): WhileStatement {
        return super.visit(whileStatement) as WhileStatement
    }

    override fun visit(unaryExpression: UnaryExpression): Expression {
        return super.visit(unaryExpression) as UnaryExpression
    }

    override fun visit(typeDeclarations: TypeDeclarations): TypeDeclarations {
        return super.visit(typeDeclarations) as TypeDeclarations
    }

    override fun visit(caseStatement: CaseStatement): CaseStatement {
        return super.visit(caseStatement) as CaseStatement
    }

    override fun visit(statements: StatementList): StatementList {
        return super.visit(statements) as StatementList
    }

    override fun visit(programDeclaration: ProgramDeclaration): ProgramDeclaration {
        return super.visit(programDeclaration) as ProgramDeclaration
    }

    override fun visit(expressions: ExpressionList): ExpressionList {
        return super.visit(expressions) as ExpressionList
    }

    override fun visit(functionDeclaration: FunctionDeclaration): FunctionDeclaration {
        return super.visit(functionDeclaration) as FunctionDeclaration
    }

    override fun visit(forStatement: ForStatement): Statement {
        return super.visit(forStatement) as ForStatement
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration): FunctionBlockDeclaration {
        return super.visit(functionBlockDeclaration) as FunctionBlockDeclaration
    }

    override fun visit(ifStatement: IfStatement): Statement {
        return super.visit(ifStatement) as Statement
    }

    override fun visit(guardedStatement: GuardedStatement): GuardedStatement {
        return super.visit(guardedStatement) as GuardedStatement
    }

    override fun visit(aCase: Case): Case {
        return super.visit(aCase) as Case
    }

    override fun visit(localScope: Scope): Scope {
        return super.visit(localScope) as Scope
    }

    override fun visit(variableDeclaration: VariableDeclaration): VariableDeclaration {
        return super.visit(variableDeclaration) as VariableDeclaration
    }

    override fun visit(arrayinit: ArrayInitialization): ArrayInitialization {
        return super.visit(arrayinit) as ArrayInitialization
    }

    override fun visit(invocation: Invocation): Expression {
        return super.visit(invocation) as Invocation
    }

    override fun visit(parameter: InvocationParameter): InvocationParameter {
        return super.visit(parameter) as InvocationParameter
    }

    override fun visit(invocation: InvocationStatement): Statement {
        return super.visit(invocation) as Statement
    }

    override fun visit(stringTypeDeclaration: StringTypeDeclaration): StringTypeDeclaration {
        return super.visit(stringTypeDeclaration) as StringTypeDeclaration
    }

    override fun visit(structureInitialization: StructureInitialization): StructureInitialization {
        return super.visit(structureInitialization) as StructureInitialization
    }

    override fun visit(clazz: ClassDeclaration): ClassDeclaration {
        return super.visit(clazz) as ClassDeclaration
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration): InterfaceDeclaration {
        return super.visit(interfaceDeclaration) as InterfaceDeclaration
    }

    override fun visit(method: MethodDeclaration): MethodDeclaration {
        return super.visit(method) as MethodDeclaration
    }

    override fun visit(gvlDecl: GlobalVariableListDeclaration): GlobalVariableListDeclaration {
        return super.visit(gvlDecl) as GlobalVariableListDeclaration
    }

    override fun visit(referenceValue: ReferenceValue): ReferenceValue {
        return super.visit(referenceValue) as ReferenceValue
    }

    override fun visit(elements: PouElements): PouElements {
        return super.visit(elements) as PouElements
    }

    override fun visit(location: Location): Location {
        return super.visit(location) as Location
    }

    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration): ArrayTypeDeclaration {
        return super.visit(arrayTypeDeclaration) as ArrayTypeDeclaration
    }

    override fun visit(exitStatement: ExitStatement): ExitStatement {
        return super.visit(exitStatement) as ExitStatement
    }

    override fun visit(configurationDeclaration: ConfigurationDeclaration): ConfigurationDeclaration {
        return super.visit(configurationDeclaration) as ConfigurationDeclaration
    }

    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration): EnumerationTypeDeclaration {
        return super.visit(enumerationTypeDeclaration) as EnumerationTypeDeclaration
    }

    override fun visit(resourceDeclaration: ResourceDeclaration): ResourceDeclaration {
        return super.visit(resourceDeclaration) as ResourceDeclaration
    }

    override fun visit(returnStatement: ReturnStatement): ReturnStatement {
        return super.visit(returnStatement) as ReturnStatement
    }

    override fun visit(structureTypeDeclaration: StructureTypeDeclaration): StructureTypeDeclaration {
        return super.visit(structureTypeDeclaration) as StructureTypeDeclaration
    }

    override fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration): SubRangeTypeDeclaration {
        return super.visit(subRangeTypeDeclaration) as SubRangeTypeDeclaration
    }

    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration): SimpleTypeDeclaration {
        return super.visit(simpleTypeDeclaration) as SimpleTypeDeclaration
    }

    override fun visit(commentStatement: CommentStatement): CommentStatement {
        return super.visit(commentStatement) as CommentStatement
    }

    override fun visit(deref: Deref): Deref {
        return super.visit(deref) as Deref
    }

    override fun visit(symbolicReference: SymbolicReference): Expression {
        return super.visit(symbolicReference) as SymbolicReference
    }

    override fun visit(ptd: PointerTypeDeclaration): PointerTypeDeclaration {
        return super.visit(ptd) as PointerTypeDeclaration
    }

    override fun visit(init: IdentifierInitializer): IdentifierInitializer {
        return super.visit(init) as IdentifierInitializer
    }

    override fun visit(literal: Literal): Expression {
        return super.visit(literal) as Literal
    }

    override fun visit(sfcStep: SFCStep): SFCStep {
        return super.visit(sfcStep) as SFCStep
    }

    override fun visit(actionDeclaration: ActionDeclaration): ActionDeclaration {
        return super.visit(actionDeclaration) as ActionDeclaration
    }

    override fun visit(sfcNetwork: SFCNetwork): SFCNetwork {
        return super.visit(sfcNetwork) as SFCNetwork
    }

    override fun visit(sfc: SFCImplementation): SFCImplementation {
        return super.visit(sfc) as SFCImplementation
    }

    override fun visit(transition: SFCTransition): SFCTransition {
        return super.visit(transition) as SFCTransition
    }

    override fun visit(referenceSpecification: ReferenceTypeDeclaration): ReferenceTypeDeclaration {
        return super.visit(referenceSpecification) as ReferenceTypeDeclaration
    }

    override fun visit(empty: EMPTY_EXPRESSION): EMPTY_EXPRESSION {
        return super.visit(empty) as EMPTY_EXPRESSION
    }
}