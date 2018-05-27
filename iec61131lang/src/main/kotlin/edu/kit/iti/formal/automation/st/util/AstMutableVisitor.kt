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
import edu.kit.iti.formal.automation.sfclang.ast.*
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.Visitable
import lombok.`val`

import java.util.ArrayList
import java.util.LinkedList
import java.util.stream.Collectors

/**
 *
 * AstMutableVisitor class.
 * This visitors defines all function with go down and setting the results of accept as the new value.
 * Not copying datastructures.
 *
 * @author Alexander Weigl (26.06.2014), Augusto Modanese
 */
open class AstMutableVisitor : AstVisitor<Any>() {
    /**
     * {@inheritDoc}
     */
    override fun defaultVisit(visitable: Visitable): Any? {
        //System.out.println("AstTransform.defaultVisit");
        //System.err.println(("maybe not fully and right supported " + visitable.getClass()));
        return visitable
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(assignmentStatement: AssignmentStatement): Any? {
        assignmentStatement.expression = assignmentStatement.expression.accept<Any>(this) as Expression
        assignmentStatement.location = assignmentStatement.location.accept<Any>(this) as Reference
        return assignmentStatement
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(integerCondition: CaseCondition.IntegerCondition): Any? {
        val sv = integerCondition.value!!.accept<Any>(this) as Literal
        integerCondition.value = sv
        return integerCondition
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(enumeration: CaseCondition.Enumeration): Any? {
        enumeration.start = enumeration.start.accept<Any>(this) as Literal
        enumeration.stop = enumeration.stop!!.accept<Any>(this) as Literal
        return enumeration
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(binaryExpression: BinaryExpression): Any? {
        binaryExpression.leftExpr = binaryExpression.leftExpr!!.accept<Any>(this) as Expression

        binaryExpression.rightExpr = binaryExpression.rightExpr!!.accept<Any>(this) as Expression

        return binaryExpression
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(unaryExpression: UnaryExpression): Any? {
        unaryExpression.expression = unaryExpression.expression.accept<Any>(this) as Expression
        return unaryExpression
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(repeatStatement: RepeatStatement): Any? {
        repeatStatement.condition = repeatStatement.condition.accept<Any>(this) as Expression
        repeatStatement.statements = repeatStatement.statements.accept(this) as StatementList
        return repeatStatement
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(whileStatement: WhileStatement): Any? {
        whileStatement.condition = whileStatement.condition.accept<Any>(this) as Expression
        whileStatement.statements = whileStatement.statements.accept(this) as StatementList
        return whileStatement
    }


    /**
     * {@inheritDoc}
     */
    override fun visit(caseStatement: CaseStatement): Any? {
        val l = LinkedList<CaseStatement.Case>()
        for (c in caseStatement.cases) {
            l.add(c.accept<Any>(this) as CaseStatement.Case)
        }

        caseStatement.cases = l

        caseStatement.expression = caseStatement.expression!!.accept<Any>(this) as Expression
        caseStatement.elseCase = caseStatement.elseCase!!.accept(this) as StatementList
        return caseStatement
    }


    /*
    @Override
    public Object accept(SymbolicReference symbolicReference) {

        if (symbolicReference.getSub() != null)
            symbolicReference.setSub((Reference) symbolicReference.getSub().accept(this));

        if (symbolicReference.getSubscripts() != null)
            symbolicReference.setSubscripts((ExpressionList)
                    symbolicReference.getSubscripts().accept(this));

        return symbolicReference;
    }*/

    /**
     * {@inheritDoc}
     */
    override fun visit(statements: StatementList): Any? {
        val r = StatementList()
        for (s in statements) {
            if (s == null) continue
            val stmt = s.accept<Any>(this)
            if (stmt is StatementList) {
                r.addAll(stmt)
            } else
                r.add(stmt as Statement)
        }
        return r
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(programDeclaration: ProgramDeclaration): Any? {
        currentTopLevelScopeElement = programDeclaration
        programDeclaration.scope = programDeclaration.scope.accept(this) as Scope
        programDeclaration.stBody = programDeclaration.stBody!!.accept(this) as StatementList
        return programDeclaration
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(invocation: Invocation): Any? {
        invocation.callee = invocation.callee.accept<Any>(this) as SymbolicReference
        invocation.parameters = invocation.parameters.stream()
                .map { p -> p.accept(this) as Invocation.Parameter }.collect<List<Parameter>, Any>(Collectors.toList<Parameter>())
        return invocation
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(forStatement: ForStatement): Any? {
        forStatement.start = forStatement.start!!.accept<Any>(this) as Expression
        forStatement.statements = forStatement.statements.accept(this) as StatementList
        if (forStatement.step != null)
            forStatement.step = forStatement.step!!.accept<Any>(this) as Expression
        forStatement.stop = forStatement.stop!!.accept<Any>(this) as Expression
        return forStatement
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(i: IfStatement): Any? {
        val guards = LinkedList<GuardedStatement>()
        for (gc in i.conditionalBranches) {
            guards.add(gc.accept<Any>(this) as GuardedStatement)
        }
        i.conditionalBranches = guards
        i.elseBranch = i.elseBranch.accept(this) as StatementList
        return i
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(commentStatement: CommentStatement): Any? {
        return commentStatement
    }


    /**
     * {@inheritDoc}
     */
    override fun visit(guardedStatement: GuardedStatement): Any? {
        guardedStatement.condition = guardedStatement.condition.accept<Any>(this) as Expression
        guardedStatement.statements = guardedStatement.statements.accept(this) as StatementList
        return guardedStatement
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(fbc: InvocationStatement): Any? {
        fbc.invocation = fbc.invocation.accept<Any>(this) as Invocation
        return fbc
    }

    override fun visit(parameter: Invocation.Parameter): Any? {
        parameter.expression = parameter.expression!!.accept<Any>(this) as Expression
        return parameter
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(aCase: CaseStatement.Case): Any? {
        val v = this.visitList<CaseCondition>(aCase.conditions)
        aCase.conditions = v
        aCase.statements = aCase.statements.accept(this) as StatementList
        return aCase
    }

    private fun <T> visitList(list: List<Visitable>): List<T> {
        val l = ArrayList()
        for (v in list)
            l.add(v.accept(this))
        return l
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration): Any? {
        return arrayTypeDeclaration
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(exitStatement: ExitStatement): Any? {
        return exitStatement
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(range: CaseCondition.Range): Any? {
        range.start = range.start!!.accept<Any>(this) as Literal
        range.stop = range.stop!!.accept<Any>(this) as Literal
        return super.visit(range)
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(configurationDeclaration: ConfigurationDeclaration): Any? {
        return configurationDeclaration
    }


    /**
     * {@inheritDoc}
     */
    override fun visit(localScope: Scope): Any? {
        currentScope = localScope
        for (variable in localScope) {
            //assert variable.getParent() != null;
            val newVariable = variable.accept<Any>(this) as VariableDeclaration
            if (newVariable == null)
                localScope.variables.remove(variable.name)
            else
                localScope.variables.replace(variable.name, newVariable)
        }
        return localScope
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(variableDeclaration: VariableDeclaration): Any? {
        variableDeclaration.setTypeDeclaration(
                variableDeclaration.typeDeclaration!!.accept(this) as TypeDeclaration<*>)

        return variableDeclaration
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(initializations: ArrayInitialization): Any? {
        return initializations
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration): Any? {
        return enumerationTypeDeclaration
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(typeDeclarations: TypeDeclarations): Any? {
        val td = TypeDeclarations()
        for (t in typeDeclarations)
            td.add(t.accept(this) as TypeDeclaration<*>)
        return td
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(expressions: ExpressionList): Any? {
        val expressionList = ExpressionList()
        for (e in expressions)
            expressionList.add(e.accept<Any>(this) as Expression)
        return expressionList
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(functionDeclaration: FunctionDeclaration): Any? {
        functionDeclaration.scope = functionDeclaration.scope.accept(this) as Scope
        functionDeclaration.stBody = functionDeclaration.stBody.accept(this) as StatementList
        return functionDeclaration
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(resourceDeclaration: ResourceDeclaration): Any? {
        return resourceDeclaration
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(fbd: FunctionBlockDeclaration): FunctionBlockDeclaration? {
        if (fbd.stBody != null)
            fbd.stBody = fbd.stBody!!.accept(this) as StatementList
        if (fbd.sfcBody != null)
            fbd.sfcBody = fbd.sfcBody!!.accept(this) as SFCImplementation

        //TODO
        /*for (ActionDeclaration action : fbd.getActions()) {
            visit(action);
        }*/
        return fbd
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(returnStatement: ReturnStatement): Any? {
        return returnStatement
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(stringTypeDeclaration: StringTypeDeclaration): Any? {
        return stringTypeDeclaration
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(structureTypeDeclaration: StructureTypeDeclaration): Any? {
        return structureTypeDeclaration
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration): Any? {
        return subRangeTypeDeclaration
    }

    /**
     * {@inheritDoc}
     */
    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration<*>): Any? {
        return super.visit(simpleTypeDeclaration)
    }


    /**
     * {@inheritDoc}
     */
    override fun visit(structureInitialization: StructureInitialization): Any? {
        return super.visit(structureInitialization)
    }

    override fun visit(location: Location): Any? {
        return super.visit(location)
    }

    override fun visit(deref: Deref): Any? {
        return super.visit(deref)
    }

    override fun visit(symbolicReference: SymbolicReference): Any? {
        if (symbolicReference.hasSubscripts())
            symbolicReference.subscripts = symbolicReference.subscripts!!.accept<Any>(this) as ExpressionList
        return super.visit(symbolicReference)
    }

    override fun visit(referenceValue: ReferenceValue): Any? {
        referenceValue.referenceTo = referenceValue.referenceTo.accept<Any>(this) as SymbolicReference
        return super.visit(referenceValue)
    }

    override fun visit(ptd: PointerTypeDeclaration): Any? {
        return super.visit(ptd)
    }

    override fun visit(init: IdentifierInitializer): Any? {
        return super.visit(init)
    }

    override fun visit(clazz: ClassDeclaration): Any? {
        currentTopLevelScopeElement = clazz
        clazz.scope = clazz.scope.accept(this) as Scope

        val methods = ArrayList<MethodDeclaration>(clazz.methods.size)
        for (method in clazz.methods) {
            val newMethod = method.accept(this) as MethodDeclaration
            if (newMethod != null)
                methods.add(newMethod)
        }
        clazz.setMethods(methods)

        return super.visit(clazz)
    }

    override fun visit(method: MethodDeclaration): Any? {
        method.scope = method.scope.accept(this) as Scope
        method.stBody = method.stBody.accept(this) as StatementList
        return super.visit(method)
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration): Any? {
        currentTopLevelScopeElement = interfaceDeclaration
        val methods = ArrayList<MethodDeclaration>(interfaceDeclaration.methods.size)
        for (method in interfaceDeclaration.methods) {
            val newMethod = method.accept(this) as MethodDeclaration
            if (newMethod != null)
                methods.add(method)
        }
        interfaceDeclaration.methods = methods
        return super.visit(interfaceDeclaration)
    }

    override fun visit(globalVariableListDeclaration: GlobalVariableListDeclaration): Any? {
        currentTopLevelScopeElement = globalVariableListDeclaration
        globalVariableListDeclaration.scope = visit(globalVariableListDeclaration.scope) as Scope?
        return super.visit(globalVariableListDeclaration)
    }

    override fun visit(literal: Literal): Any? {
        return super.visit(literal)
    }


    override fun visit(referenceSpecification: ReferenceSpecification): Any? {
        return super.visit(referenceSpecification)
    }

    override fun visit(sfcStep: SFCStep): Any? {
        return super.visit(sfcStep)
    }

    override fun visit(actionDeclaration: ActionDeclaration): Any? {
        return super.visit(actionDeclaration)
    }

    override fun visit(sfcNetwork: SFCNetwork): Any? {
        return super.visit(sfcNetwork)
    }

    override fun visit(sfc: SFCImplementation): Any? {
        return super.visit(sfc)
    }

    override fun visit(transition: SFCTransition): Any? {
        return super.visit(transition)
    }
}
