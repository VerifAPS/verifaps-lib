package edu.kit.iti.formal.automation.st.util

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
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import java.util.*

/**
 * Created by weigl on 10/07/14.
 *
 * @author weigl
 * @version $Id: $Id
 */

open class AstVisitor<T> : DefaultVisitor<T>() {
    //protected lateinit var scope: Scope
    //protected val stack: Stack<Top> = Stack()

    override fun defaultVisit(obj: Any?): T? {
        return null//throw new Error("not implemented for " + visitable.getClass());
    }

    override fun visit(assignmentStatement: AssignmentStatement): T? {
        assignmentStatement.expression.accept(this)
        assignmentStatement.location.accept(this)
        return defaultVisit(assignmentStatement)
    }


    /**
     * {@inheritDoc}
     */
    override fun visit(range: CaseCondition.Range): T? {
        range.start!!.accept(this)
        range.stop!!.accept(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(integerCondition: CaseCondition.IntegerCondition): T? {
        integerCondition.value.accept(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(enumeration: CaseCondition.Enumeration): T? {
        enumeration.start.accept(this)
        enumeration.stop!!.accept(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(binaryExpression: BinaryExpression): T? {
        binaryExpression.leftExpr.accept(this)
        binaryExpression.rightExpr.accept(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(repeatStatement: RepeatStatement): T? {
        repeatStatement.condition.accept(this)
        repeatStatement.statements.accept(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(whileStatement: WhileStatement): T? {
        whileStatement.condition.accept(this)
        whileStatement.statements.accept(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(unaryExpression: UnaryExpression): T? {
        unaryExpression.expression.accept(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(typeDeclarations: TypeDeclarations): T? {
        for (td in typeDeclarations)
            td.accept(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(caseStatement: CaseStatement): T? {
        caseStatement.expression.accept(this)
        for (c in caseStatement.cases)
            c.accept(this)

        caseStatement.elseCase!!.accept(this)

        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(statements: StatementList): T? {
        for (s in statements)
            s.accept(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(programDeclaration: ProgramDeclaration): T? {
        programDeclaration.scope.accept(this)
        programDeclaration.stBody!!.accept(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(expressions: ExpressionList): T? {
        for (e in expressions)
            e.accept(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(functionDeclaration: FunctionDeclaration): T? {
        functionDeclaration.scope.accept(this)
        functionDeclaration.stBody.accept(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(forStatement: ForStatement): T? {
        forStatement.start!!.accept(this)
        if (forStatement.step != null)
            forStatement.step!!.accept(this)
        forStatement.stop!!.accept(this)
        forStatement.statements.accept(this)
        return null
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration): T? {
        //currentFullScope = OOUtils.getEffectiveScope(functionBlockDeclaration);
        if (functionBlockDeclaration.stBody != null)
            functionBlockDeclaration.stBody!!.accept(this)
        if (functionBlockDeclaration.sfcBody != null)
            functionBlockDeclaration.sfcBody!!.accept(this)
        return null//functionBlockDeclaration;
    }


    /**
     * {@inheritDoc}
     */
    override fun visit(ifStatement: IfStatement): T? {
        for (gs in ifStatement.conditionalBranches)
            gs.accept(this)

        ifStatement.elseBranch.accept(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(guardedStatement: GuardedStatement): T? {
        guardedStatement.condition.accept(this)
        guardedStatement.statements.accept(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(aCase: Case): T? {
        aCase.statements.accept(this)
        for (c in aCase.conditions)
            c.accept(this)
        return null
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(localScope: Scope): T? {
        for (vd in localScope)
            vd.accept(this)
        return defaultVisit(localScope)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(variableDeclaration: VariableDeclaration): T? {
        if (null != variableDeclaration.typeDeclaration) {
            variableDeclaration.typeDeclaration!!.accept(this)
        }

        if (null != variableDeclaration.init) {
            variableDeclaration.init!!.accept(this)
        }

        return super.visit(variableDeclaration)
    }

    override fun visit(arrayinit: ArrayInitialization): T? {
        for (init in arrayinit.initValues)
            init.accept(this)
        return super.visit(arrayinit)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(invocation: Invocation): T? {
        invocation.callee.accept(this)
        invocation.parameters.forEach { e -> e.accept(this) }
        return super.visit(invocation)
    }

    override fun visit(parameter: InvocationParameter): T? {
        parameter.expression.accept(this)
        return super.visit(parameter)
    }

    override fun visit(invocation: InvocationStatement): T? {
        invocation.invocation.accept(this)
        return super.visit(invocation)
    }

    override fun visit(stringTypeDeclaration: StringTypeDeclaration): T? {
        if (stringTypeDeclaration.initialization != null)
            stringTypeDeclaration.initialization!!.accept(this)
        return super.visit(stringTypeDeclaration)
    }

    override fun visit(structureInitialization: StructureInitialization): T? {
        structureInitialization.initValues.values.forEach { v -> v.accept(this) }
        return super.visit(structureInitialization)
    }

    override fun visit(clazz: ClassDeclaration): T? {
        clazz.scope.accept(this)
        for (m in ArrayList(clazz.methods)) {
            m.accept(this)
        }
        return super.visit(clazz)
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration): T? {
        //TODO inferface? interfaceDeclaration.scope.accept(this)
        for (m in interfaceDeclaration.methods)
            m.accept(this)
        return super.visit(interfaceDeclaration)
    }

    override fun visit(method: MethodDeclaration): T? {
        method.scope.accept(this)
        if (method.stBody != null)
            method.stBody.accept(this)
        return defaultVisit(method)
    }

    override fun visit(globalVariableListDeclaration: GlobalVariableListDeclaration): T? {
        globalVariableListDeclaration.scope.accept(this)
        return super.visit(globalVariableListDeclaration)
    }

    override fun visit(referenceValue: ReferenceValue): T? {
        referenceValue.referenceTo.accept(this)
        return super.visit(referenceValue)
    }

}


open class AstVisitorWithScope<T> : AstVisitor<T>() {
    protected lateinit var scope: Scope
    override fun visit(localScope: Scope): T? {
        scope = localScope
        return super.visit(localScope)
    }
}
