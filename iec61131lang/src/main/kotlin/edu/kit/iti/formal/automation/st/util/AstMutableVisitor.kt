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
import edu.kit.iti.formal.automation.visitors.Visitable
import java.util.*

/**
 *
 * AstMutableVisitor class.
 * This visitors defines all function with go down and setting the results of accept as the new value.
 * Not copying datastructures.
 *
 * @author Alexander Weigl (26.06.2014), Augusto Modanese
 */
open class AstMutableVisitor : AstVisitor<Any>() {
    override fun defaultVisit(obj: Any?): Any? {
        //System.out.println("AstTransform.defaultVisit");
        //System.err.println(("maybe not fully and right supported " + visitable.getClass()));
        return obj
    }

    override fun visit(assignmentStatement: AssignmentStatement): Any? {
        assignmentStatement.expression = assignmentStatement.expression.accept(this) as Expression
        assignmentStatement.location = assignmentStatement.location.accept(this) as Reference
        return assignmentStatement
    }


    override fun visit(integerCondition: CaseCondition.IntegerCondition): Any? {
        val sv = integerCondition.value!!.accept(this) as Literal
        integerCondition.value = sv
        return integerCondition
    }


    override fun visit(enumeration: CaseCondition.Enumeration): Any? {
        enumeration.start = enumeration.start.accept(this) as Literal
        enumeration.stop = enumeration.stop!!.accept(this) as Literal
        return enumeration
    }


    override fun visit(binaryExpression: BinaryExpression): Any? {
        binaryExpression.leftExpr = binaryExpression.leftExpr!!.accept(this) as Expression

        binaryExpression.rightExpr = binaryExpression.rightExpr!!.accept(this) as Expression

        return binaryExpression
    }


    override fun visit(unaryExpression: UnaryExpression): Any? {
        unaryExpression.expression = unaryExpression.expression.accept(this) as Expression
        return unaryExpression
    }


    override fun visit(repeatStatement: RepeatStatement): Any? {
        repeatStatement.condition = repeatStatement.condition.accept(this) as Expression
        repeatStatement.statements = repeatStatement.statements.accept(this) as StatementList
        return repeatStatement
    }


    override fun visit(whileStatement: WhileStatement): Any? {
        whileStatement.condition = whileStatement.condition.accept(this) as Expression
        whileStatement.statements = whileStatement.statements.accept(this) as StatementList
        return whileStatement
    }


    override fun visit(caseStatement: CaseStatement): Any? {
        val l = LinkedList<Case>()
        for (c in caseStatement.cases) {
            l.add(c.accept(this) as Case)
        }

        caseStatement.cases.clear()
        caseStatement.cases.addAll(l)

        caseStatement.expression = caseStatement.expression!!.accept(this) as Expression
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


    override fun visit(statements: StatementList): Any? {
        val r = StatementList()
        for (s in statements) {
            if (s == null) continue
            val stmt = s.accept(this)
            if (stmt is StatementList) {
                r.addAll(stmt)
            } else
                r.add(stmt as Statement)
        }
        return r
    }


    override fun visit(programDeclaration: ProgramDeclaration): Any? {
        programDeclaration.scope = programDeclaration.scope.accept(this) as Scope
        programDeclaration.stBody = programDeclaration.stBody!!.accept(this) as StatementList
        return programDeclaration
    }


    override fun visit(invocation: Invocation): Any? {
        invocation.callee = invocation.callee.accept(this) as SymbolicReference
        invocation.parameters.setAll(
                invocation.parameters
                        .map { p -> p.accept(this) as InvocationParameter }
        )
        return invocation
    }


    override fun visit(forStatement: ForStatement): Any? {
        forStatement.start = forStatement.start!!.accept(this) as Expression
        forStatement.statements = forStatement.statements.accept(this) as StatementList
        if (forStatement.step != null)
            forStatement.step = forStatement.step!!.accept(this) as Expression
        forStatement.stop = forStatement.stop!!.accept(this) as Expression
        return forStatement
    }


    override fun visit(i: IfStatement): Any? {
        val guards = LinkedList<GuardedStatement>()
        for (gc in i.conditionalBranches) {
            guards.add(gc.accept(this) as GuardedStatement)
        }
        i.conditionalBranches.clear()
        i.conditionalBranches.setAll(guards)
        i.elseBranch = i.elseBranch.accept(this) as StatementList
        return i
    }


    override fun visit(commentStatement: CommentStatement): Any? {
        return commentStatement
    }


    override fun visit(guardedStatement: GuardedStatement): Any? {
        guardedStatement.condition = guardedStatement.condition.accept(this) as Expression
        guardedStatement.statements = guardedStatement.statements.accept(this) as StatementList
        return guardedStatement
    }


    override fun visit(fbc: InvocationStatement): Any? {
        fbc.invocation = fbc.invocation.accept(this) as Invocation
        return fbc
    }

    override fun visit(parameter: InvocationParameter): Any? {
        parameter.expression = parameter.expression!!.accept(this) as Expression
        return parameter
    }


    override fun visit(aCase: Case): Any? {
        val v = this.visitList<CaseCondition>(aCase.conditions)
        aCase.conditions.setAll(v)
        aCase.statements = aCase.statements.accept(this) as StatementList
        return aCase
    }

    private fun <T> visitList(list: List<Visitable>): MutableList<T> {
        val l = arrayListOf<T>()
        for (v in list)
            l.add(v.accept(this) as T)
        return l
    }


    override fun visit(arrayTypeDeclaration: ArrayTypeDeclaration): Any? {
        return arrayTypeDeclaration
    }


    override fun visit(exitStatement: ExitStatement): Any? {
        return exitStatement
    }


    override fun visit(range: CaseCondition.Range): Any? {
        range.start = range.start!!.accept(this) as Literal
        range.stop = range.stop!!.accept(this) as Literal
        return super.visit(range)
    }


    override fun visit(configurationDeclaration: ConfigurationDeclaration): Any? {
        return configurationDeclaration
    }


    override fun visit(localScope: Scope): Any? {
        for (variable in localScope) {
            //assert variable.getParent() != null;
            val newVariable = variable.accept(this) as VariableDeclaration
            if (newVariable == null)
                localScope.variables.remove(variable.name)
            else
                localScope.variables.replace(variable.name, newVariable)
        }
        return localScope
    }


    override fun visit(variableDeclaration: VariableDeclaration): Any? {
        variableDeclaration.typeDeclaration = variableDeclaration.typeDeclaration!!.accept(this) as TypeDeclaration
        return variableDeclaration
    }


    override fun visit(arrayinit: ArrayInitialization): Any? {
        return arrayinit
    }


    override fun visit(enumerationTypeDeclaration: EnumerationTypeDeclaration): Any? {
        return enumerationTypeDeclaration
    }


    override fun visit(typeDeclarations: TypeDeclarations): Any? {
        val td = TypeDeclarations()
        for (t in typeDeclarations)
            td.add(t.accept(this) as TypeDeclaration)
        return td
    }


    override fun visit(expressions: ExpressionList): Any? {
        val expressionList = ExpressionList()
        for (e in expressions)
            expressionList.add(e.accept(this) as Expression)
        return expressionList
    }


    override fun visit(functionDeclaration: FunctionDeclaration): Any? {
        functionDeclaration.scope = functionDeclaration.scope.accept(this) as Scope
        functionDeclaration.stBody = functionDeclaration.stBody.accept(this) as StatementList
        return functionDeclaration
    }


    override fun visit(resourceDeclaration: ResourceDeclaration): Any? {
        return resourceDeclaration
    }


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


    override fun visit(returnStatement: ReturnStatement): Any? {
        return returnStatement
    }


    override fun visit(stringTypeDeclaration: StringTypeDeclaration): Any? {
        return stringTypeDeclaration
    }


    override fun visit(structureTypeDeclaration: StructureTypeDeclaration): Any? {
        return structureTypeDeclaration
    }


    override fun visit(subRangeTypeDeclaration: SubRangeTypeDeclaration): Any? {
        return subRangeTypeDeclaration
    }


    override fun visit(simpleTypeDeclaration: SimpleTypeDeclaration): Any? {
        return super.visit(simpleTypeDeclaration)
    }


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
            symbolicReference.subscripts = symbolicReference.subscripts!!.accept(this) as ExpressionList
        return super.visit(symbolicReference)
    }

    override fun visit(referenceValue: ReferenceValue): Any? {
        referenceValue.referenceTo = referenceValue.referenceTo.accept(this) as SymbolicReference
        return super.visit(referenceValue)
    }

    override fun visit(ptd: PointerTypeDeclaration): Any? {
        return super.visit(ptd)
    }

    override fun visit(init: IdentifierInitializer): Any? {
        return super.visit(init)
    }

    override fun visit(clazz: ClassDeclaration): Any? {
        clazz.scope = clazz.scope.accept(this) as Scope

        val methods = ArrayList<MethodDeclaration>(clazz.methods.size)
        for (method in clazz.methods) {
            val newMethod = method.accept(this) as MethodDeclaration
            if (newMethod != null)
                methods.add(newMethod)
        }
        //clazz.setMethods(methods)

        return super.visit(clazz)
    }

    override fun visit(method: MethodDeclaration): Any? {
        method.scope = method.scope.accept(this) as Scope
        method.stBody = method.stBody.accept(this) as StatementList
        return super.visit(method)
    }

    override fun visit(interfaceDeclaration: InterfaceDeclaration): Any? {
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
        globalVariableListDeclaration.scope = (globalVariableListDeclaration.scope.accept(this) as Scope?)!!
        return super.visit(globalVariableListDeclaration)
    }

    override fun visit(literal: Literal): Any? {
        return super.visit(literal)
    }

    override fun visit(referenceSpecification: ReferenceTypeDeclaration): Any? {
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

fun <E> MutableCollection<E>.setAll(seq: Collection<E>) {
    this.clear()
    this.addAll(seq)
}
