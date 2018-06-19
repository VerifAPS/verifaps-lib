package edu.kit.iti.formal.automation.smv

/*-
 * #%L
 * iec-symbex
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

import edu.kit.iti.formal.automation.datatypes.EnumerateType
import edu.kit.iti.formal.automation.datatypes.values.VAnyEnum
import edu.kit.iti.formal.automation.exceptions.*
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.smv.translators.*
import edu.kit.iti.formal.automation.st.DefaultInitValue
import edu.kit.iti.formal.automation.st.InitValueTranslator
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.ast.*
import java.util.*

/**
 * Created by weigl on 26.11.16.
 */
open class SymbolicExecutioner() : DefaultVisitor<SMVExpr>() {
    override fun defaultVisit(obj: Any) = TODO()

    //region getter and setters
    var scope: Scope? = Scope.defaultScope()
    private val varCache = HashMap<String, SVariable>()
    var operationMap: OperationMap = DefaultOperationMap()
    var typeTranslator: TypeTranslator = DefaultTypeTranslator()
    var valueTranslator: ValueTranslator = DefaultValueTranslator()
    var initValueTranslator: InitValueTranslator = DefaultInitValue

    //region state handling
    private val state = Stack<SymbolicState>()
    private var globalState = SymbolicState()
    private var caseExpression: Expression? = null

    init {
        push(SymbolicState(globalState))
    }

    constructor(globalScope: Scope?) : this() {
        if (globalScope != null)
            this.scope = globalScope
    }
    //endregion

    fun peek(): SymbolicState {
        return state.peek()
    }

    fun pop(): SymbolicState {
        return state.pop()
    }
    //endregion

    @JvmOverloads
    fun push(map: SymbolicState = SymbolicState(peek())) {
        state.push(map)
    }

    fun lift(vd: VariableDeclaration): SVariable {
        try {
            /*
            if (vd.dataType == null) {
                vd.dataType = scope!!.resolveDataType(vd.dataType)
            }*/
            return varCache.computeIfAbsent(vd.name) { this.typeTranslator.translate(vd) }
        } catch (e: NullPointerException) {
            throw UnknownDatatype("Datatype not given/inferred for variable " + vd.name, e)
        }

    }

    fun lift(vd: SymbolicReference): SVariable {
        return if (varCache.containsKey(vd.identifier))
            varCache[vd.identifier]!!
        else
            throw UnknownVariableException("Variable access to not declared variable: $vd")
    }

    //region rewriting of expressions using the current state
    override fun visit(binaryExpression: BinaryExpression): SMVExpr {
        val left = binaryExpression.leftExpr.accept(this)!!
        val right = binaryExpression.rightExpr.accept(this)!!
        return this.operationMap
                .translateBinaryOperator(left, binaryExpression.operator, right)
    }

    override fun visit(u: UnaryExpression): SMVExpr {
        val left = u.expression.accept(this)!!
        return this.operationMap.translateUnaryOperator(u.operator, left)
    }

    override fun visit(symbolicReference: SymbolicReference): SMVExpr {
        if (symbolicReference.dataType == null && !symbolicReference.hasSub()) {
            // TODO fix this dirty workaround
            try {
                symbolicReference.dataType = scope!!.resolveDataType(symbolicReference.identifier)
            } catch (ignored: DataTypeNotDefinedException) {
                // pass
            } catch (ignored: ClassCastException) {
            }

        }
        return if (symbolicReference.dataType is EnumerateType && (symbolicReference.dataType as EnumerateType)
                        .allowedValues.contains(symbolicReference.identifier))
            this.valueTranslator.translate(VAnyEnum(
                    symbolicReference.dataType as EnumerateType,
                    symbolicReference.identifier))
        else
            peek()[lift(symbolicReference)]!!
    }

    //endregion

    override fun visit(literal: Literal): SLiteral {
        return this.valueTranslator.translate(literal)
    }

    override fun visit(programDeclaration: ProgramDeclaration): SCaseExpression? {
        scope = programDeclaration.scope

        push(SymbolicState(scope!!.asMap().size))

        // initialize root state
        for (vd in scope!!) {
            val s = lift(vd)
            peek()[s] = s
        }

        globalState = SymbolicState()
        for (variable in scope!!.filterByFlags(VariableDeclaration.GLOBAL))
            globalState[lift(variable)] = peek()[lift(variable)]!!

        programDeclaration.stBody!!.accept(this)
        return null
    }

    override fun visit(assign: AssignmentStatement): SMVExpr? {
        val s = peek()
        s[lift(assign.location as SymbolicReference)] = assign.expression.accept(this)!!
        return null
    }

    override fun visit(statements: StatementList): SCaseExpression? {
        for (s in statements) {
            if (s is ExitStatement) {
                return null
            }
            s.accept(this)
        }
        return null
    }

    override fun visit(fbc: InvocationStatement): SMVExpr {
        return visit(fbc.invocation)!!
    }

    override fun visit(invocation: Invocation): SMVExpr? {
        assert(scope != null)
        val fd = scope!!.resolveFunction(invocation) ?: throw FunctionUndefinedException(invocation)

//initialize data structure
        val calleeState = SymbolicState(globalState)
        val callerState = peek()

        //region register function name as output variable
        if (null == fd.scope.getVariable(fd.name)) {//&& fd.getReturnType() != null) {
            fd.scope.builder()
                    .baseType(fd.returnType.identifier!!)
                    .push(VariableDeclaration.OUTPUT)
                    .identifiers(fd.name)
                    .create()
        }
        //endregion

        //region local variables (declaration and initialization)
        for (vd in fd.scope.variables) {
            //if (!calleeState.containsKey(vd.getName())) {
            val td = vd.typeDeclaration
            if (td != null && td!!.initialization != null) {
                td!!.initialization!!.accept(this)
            } else {
                calleeState[lift(vd)] = this.valueTranslator.translate(
                        this.initValueTranslator.getInit(vd.dataType!!))
            }
            //}
        }
        //endregion

        //region transfer variables
        val parameters = invocation.parameters
        val inputVars = fd.scope.filterByFlags(
                VariableDeclaration.INPUT or VariableDeclaration.INOUT or VariableDeclaration.OUTPUT)

        if (parameters.size > inputVars.size) {
            //System.err.println(fd.getFunctionName());
            //inputVars.stream().map(VariableDeclaration::getName).forEach(System.err::println);
            throw FunctionInvocationArgumentNumberException()
        }

        for (i in parameters.indices) {
            val parameter = parameters[i]
            if (parameter.isOutput)
                continue
            if (parameter.name == null)
            // name from definition, in order of declaration, expression from caller site
                calleeState[lift(inputVars[i])] = parameter.expression.accept(this)!!
            else {
                val o = inputVars.stream().filter { iv -> iv.name == parameter.name }.findAny()
                if (o.isPresent) {
                    val e = parameter.expression.accept(this)!!
                    calleeState[lift(o.get())] = e!!
                }
            }
        }

        for (outputVar in fd.scope.filterByFlags(VariableDeclaration.OUTPUT))
            calleeState[lift(outputVar)] = this.valueTranslator.translate(
                    this.initValueTranslator.getInit(outputVar.dataType!!))

        push(calleeState)
        //endregion

        // execution of body
        fd.stBody?.accept(this)

        val returnState = pop()
        // Update output variables
        val outputParameters = invocation.outputParameters
        val outputVars = fd.scope.filterByFlags(
                VariableDeclaration.OUTPUT, VariableDeclaration.INOUT)
        for (parameter in outputParameters) {
            val o = outputVars.stream().filter { iv -> iv.name == parameter.name }.findAny()
            if (o.isPresent && parameter.expression is SymbolicReference
                    && (parameter.expression as SymbolicReference).dataType !is EnumerateType)
                peek().replace(lift(parameter.expression as SymbolicReference),
                        returnState[lift(o.get())]!!)
            // TODO handle parameter.getExpression() instanceof Literal, etc.
        }

        //fd.getReturnType() != null
        calleeState[lift(Objects.requireNonNull<VariableDeclaration>(fd.scope.getVariable(fd.name)))]
        //: null;
        return null
    }

    //endregion

    override fun visit(statement: IfStatement): SCaseExpression? {
        val branchStates = SymbolicBranches()

        for ((condition1, statements) in statement.conditionalBranches) {
            val condition = condition1.accept(this)!!
            push()
            statements.accept(this)
            branchStates.addBranch(condition, pop())
        }

        push()
        statement.elseBranch.accept(this)
        branchStates.addBranch(SLiteral.TRUE, pop())

        peek().putAll(branchStates.asCompressed())
        return null
    }

    override fun visit(caseStatement: CaseStatement): SMVExpr? {
        val branchStates = SymbolicBranches()
        for (gs in caseStatement.cases) {
            val condition = buildCondition(caseStatement.expression, gs)
            push()
            gs.statements.accept(this)
            branchStates.addBranch(condition, pop())
        }
        push()
        caseStatement.elseCase!!.accept(this)
        branchStates.addBranch(SLiteral.TRUE, pop())
        peek().putAll(branchStates.asCompressed())
        return null
    }

    private fun buildCondition(e: Expression, c: Case): SMVExpr {
        caseExpression = e
        return c.conditions
                .map { a -> a.accept(this) }
                .map { it!! }
                .reduce(SMVFacade.reducerKt(SBinaryOperator.OR))
    }

    override fun visit(r: CaseCondition.Range): SMVExpr {
        val lower = BinaryExpression(caseExpression!!, Operators.GREATER_EQUALS, r.start!!)
        val upper = BinaryExpression(r.stop!!, Operators.GREATER_EQUALS, caseExpression!!)
        val and = BinaryExpression(lower, Operators.AND, upper)
        return and.accept(this)!!
    }

    override fun visit(i: CaseCondition.IntegerCondition): SMVExpr {
        val be = BinaryExpression(caseExpression!!, Operators.EQUALS, i.value)
        return be.accept(this)!!
    }


    override fun visit(e: CaseCondition.Enumeration): SMVExpr {
        val be = BinaryExpression(caseExpression!!, Operators.EQUALS, e.start)
        return be.accept(this)!!
        //TODO rework case conditions
    }
}
