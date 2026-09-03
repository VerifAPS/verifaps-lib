/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
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
 * *****************************************************************/
package edu.kit.iti.formal.automation.rvt

import edu.kit.iti.formal.automation.ASSERTION_PREFIX
import edu.kit.iti.formal.automation.ASSUMPTION_PREFIX
import edu.kit.iti.formal.automation.HAVOC_PREFIX
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.analysis.toHuman
import edu.kit.iti.formal.automation.exceptions.UnknownDatatype
import edu.kit.iti.formal.automation.exceptions.UnknownVariableException
import edu.kit.iti.formal.automation.il.IlSymbex
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.rvt.pragma.SmvBody
import edu.kit.iti.formal.automation.rvt.translators.*
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.DefaultInitValue
import edu.kit.iti.formal.automation.st.Identifiable
import edu.kit.iti.formal.automation.st.InitValueTranslator
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.ast.Invoked.*
import edu.kit.iti.formal.automation.st.util.AstVisitorWithScope
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.ast.*
import java.util.*
import java.util.concurrent.atomic.AtomicInteger
import kotlin.collections.HashMap
import kotlin.math.max

/**
 * Symbolic execution visitor for Structured Text (ST) using modern AstVisitorWithScope infrastructure.
 * 
 * This class performs symbolic execution on ST AST nodes and produces SMV expressions.
 * It uses stack-based SymbolicState management for handling control flow branches.
 * 
 * @author Alexander Weigl
 * @version 1 (2026)
 */
open class StVerificationVisitor(
    scope: Scope = Scope.defaultScope(),
    val useDefinitions: Boolean = true
) : AstVisitorWithScope<SMVExpr>() {

    init {
        this.scope = scope
    }

    override fun defaultVisit(obj: Any): SMVExpr = throw IllegalStateException("StVerificationVisitor does not handle $obj")

    private val varCache = HashMap<String, SVariable>()
    var operationMap: OperationMap = DefaultOperationMap()
    var typeTranslator: TypeTranslator = DefaultTypeTranslator()
    var valueTranslator: ValueTranslator = DefaultValueTranslator()
    var initValueTranslator: InitValueTranslator = DefaultInitValue

    private val state = Stack<SymbolicState>()
    private var globalState = SymbolicState(useDefinitions = useDefinitions)
    private var caseExpression: Expression? = null

    init {
        push(SymbolicState(globalState))
    }

    fun peek(): SymbolicState = state.peek()

    fun pop(): SymbolicState = state.pop()

    @JvmOverloads
    fun push(map: SymbolicState = SymbolicState(peek())) {
        state.push(map)
    }

    fun lift(vd: VariableDeclaration): SVariable {
        try {
            return varCache.computeIfAbsent(vd.name) { this.typeTranslator.translate(vd) }
        } catch (e: NullPointerException) {
            throw UnknownDatatype("Datatype not given/inferred for variable $vd ${vd.dataType}", e)
        }
    }

    fun lift(vd: SymbolicReference): SVariable {
        return if (varCache.containsKey(vd.identifier)) {
            varCache[vd.identifier]!!
        } else {
            val v = peek().keys.find { name ->
                vd.identifier == name.name
            }
            if (v != null) {
                varCache[vd.identifier] = v
                return v
            }
            try {
                return lift(this.scope.getVariable(vd))
            } catch (e: Exception) {
                throw UnknownVariableException(
                    "Variable access to not declared variable: ${IEC61131Facade.print(vd)}." +
                        " Line: ${vd.startPosition}",
                )
            }
        }
    }

    //region Expression visitors
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
        return peek()[lift(symbolicReference)]
            ?: throw IllegalStateException("Could not resolve access to '${symbolicReference.toHuman()}'.")
    }

    override fun visit(literal: Literal): SLiteral = this.valueTranslator.translate(literal)
    //endregion

    //region Statement visitors
    override fun visit(programDeclaration: ProgramDeclaration): SMVExpr {
        return visitPouExecutable(programDeclaration)
    }

    override fun visit(functionBlockDeclaration: FunctionBlockDeclaration): SMVExpr {
        return visitPouExecutable(functionBlockDeclaration)
    }

    override fun visit(functionDeclaration: FunctionDeclaration): SMVExpr {
        return visitPouExecutable(functionDeclaration)
    }

    private fun visitPouExecutable(exec: PouExecutable): SMVExpr {
        exec.findAttributePragma("smv_body")?.let {
            val smvBody = SmvBody(it)
            // TODO do not execute body use value of smvBody instead
            // TODO allow introduction of new smv input variables
        }

        this.scope = exec.scope

        push(SymbolicState(useDefinitions = useDefinitions))

        // initialize root state
        for (vd in this.scope) {
            val s = lift(vd)
            assign(vd, s)
        }

        globalState = SymbolicState()
        for (variable in this.scope.filterByFlags(VariableDeclaration.GLOBAL)) {
            globalState[lift(variable)] = peek()[lift(variable)]!!
        }

        exec.stBody!!.accept(this)
        return SLiteral.TRUE
    }

    override fun visit(assign: AssignmentStatement): SMVExpr {
        val expr = assign.expression.accept(this)!!
        assign(assign.location, expr)
        return expr
    }

    override fun visit(statements: StatementList): SMVExpr {
        for (s in statements) {
            if (s is ExitStatement || s is ReturnStatement) {
                return SLiteral.FALSE
            }
            s.accept(this)
        }
        return SLiteral.TRUE
    }

    override fun visit(invocation: Invocation): SMVExpr {
        val inv = when (val i = invocation.invoked) {
            is Action -> i.action
            is Program -> i.program
            is FunctionBlock -> i.fb
            is Invoked.Function -> i.function
            is Method -> i.method
            null -> throw IllegalStateException("Can not invoke a not resolved function: $invocation")
        }
        val returnType = when (val i = invocation.invoked) {
            is Invoked.Function -> i.function.returnType
            is Method -> i.method.returnType
            else -> throw IllegalStateException("$invocation does not have a return type.")
        }
        val stBody = (inv as? HasStBody)?.stBody
        val ilBody = (inv as? HasIlBody)?.ilBody
        val scope = (inv as? HasScope)?.scope!!
        val fName = (inv as Identifiable).name

        // initialize data structure
        val calleeState = SymbolicState(globalState)
        val callerState = peek()

        //region register function name as output variable
        if (scope.hasVariable(fName)) {
            val vd = VariableDeclaration(fName, VariableDeclaration.OUTPUT, returnType.obj!!)
            vd.initValue = initValueTranslator.getInit(returnType.obj!!)
            scope.add(vd)
        }
        //endregion

        //region local variables (declaration and initialization)
        for (vd in scope.variables) {
            val expr = this.valueTranslator.translate(vd.initValue!!)
            calleeState.assign(lift(vd), assignmentCounter.incrementAndGet(), expr)
        }
        //endregion

        //region transfer variables
        val parameters = invocation.parameters
        val inputVars = scope.filterByFlags(VariableDeclaration.INPUT or VariableDeclaration.INOUT)

        require(parameters.size == inputVars.size) {
            "Inappropriate number of parameters for $fName: ${parameters.size} != ${inputVars.size}"
        }

        for ((i, parameter) in parameters.withIndex()) {
            val targetVar = inputVars[i]
            val sourceExpr = parameter.expression.accept(this)!!
            calleeState.assign(lift(targetVar), assignmentCounter.incrementAndGet(), sourceExpr)
        }
        //endregion

        //region initialize output variables
        val outputVarsInit = scope.filterByFlags(VariableDeclaration.OUTPUT, VariableDeclaration.INOUT)
        for (outputVar in outputVarsInit) {
            calleeState.assign(
                lift(outputVar),
                assignmentCounter.incrementAndGet(),
                this.valueTranslator.translate(this.initValueTranslator.getInit(outputVar.dataType!!)),
            )
        }
        //endregion

        //region execution of body
        val returnState =
            if (stBody != null) {
                push(calleeState)
                stBody.accept(this)
                pop()
            } else if (ilBody != null) {
                val ilsymbex = IlSymbex(ilBody, scope = scope, state = calleeState)
                ilsymbex.call()
            } else {
                throw IllegalStateException("No executable body found for $fName")
            }

        // Update output variables
        val outputParameters = invocation.outputParameters
        val outputVarsUpdate = scope.filterByFlags(VariableDeclaration.OUTPUT, VariableDeclaration.INOUT)

        for (parameter in outputParameters) {
            val o = outputVarsUpdate.find { fName == parameter.name }
            val expr = parameter.expression
            if (o != null && parameter.expression is SymbolicReference) {
                val symVar = lift(expr as SymbolicReference)
                peek().replace(symVar, returnState[lift(o)]!!)
            }
        }
        //endregion

        val unfolded = calleeState.unfolded()
        return unfolded.entries.find { (a, b) -> a.name == fName }?.value ?: SLiteral.TRUE
    }

    override fun visit(ifStatement: IfStatement): SMVExpr {
        val iln = ifStatement.startPosition

        val branchStates = SymbolicBranches()
        var branchConditionDefinitions: SMVExpr = SLiteral.TRUE

        for ((condition1, statements) in ifStatement.conditionalBranches) {
            val condition = condition1.accept(this)!!
            push()
            statements.accept(this)
            branchStates.addBranch(condition, pop())
            assignIBC(
                iln,
                condition1.startPosition,
                branchConditionDefinitions and condition,
            )
            branchConditionDefinitions = branchConditionDefinitions and condition.not()
        }

        push()
        ifStatement.elseBranch.accept(this)
        branchStates.addBranch(SLiteral.TRUE, pop())
        assignIBC(iln, ifStatement.elseBranch.startPosition, branchConditionDefinitions)

        val cur = peek()
        val combined = branchStates.asCompressed(ifStatement.endPosition)
        cur.variables.putAll(combined.variables)
        cur.auxiliaryDefinitions.putAll(combined.auxiliaryDefinitions)
        return SLiteral.TRUE
    }

    private fun assignIBC(ifLine: Position, branchLine: Position, condition: SMVExpr) {
        val identifier = String.format(
            "bc_%03d_%03d_",
            ifLine.lineNumber,
            max(0, branchLine.lineNumber),
        )
        val key = SVariable(identifier, SMVTypes.BOOLEAN)
        peek().auxiliaryDefinitions[key] = condition
        lineNumberMap.markAsBranchCondition(identifier, ifLine, branchLine)
    }

    override fun visit(caseStatement: CaseStatement): SMVExpr {
        val branchStates = SymbolicBranches()
        var branchCondition: SMVExpr = SLiteral.TRUE
        for (gs in caseStatement.cases) {
            val condition = buildCondition(caseStatement.expression, gs)
            assignIBC(caseStatement.startPosition, gs.startPosition, branchCondition and condition)
            branchCondition = branchCondition and condition.not()
            push()
            gs.statements.accept(this)
            branchStates.addBranch(condition, pop())
        }

        if (caseStatement.elseCase.isNotEmpty()) {
            assignIBC(
                caseStatement.startPosition,
                caseStatement.elseCase.startPosition,
                branchCondition,
            )
            push()
            caseStatement.elseCase.accept(this)
            branchStates.addBranch(SLiteral.TRUE, pop())
        }
        val cur = peek()
        val combined = branchStates.asCompressed(caseStatement.endPosition)
        cur.variables.putAll(combined.variables)
        return SLiteral.TRUE
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
    }
    //endregion

    //region Ignore visitors
    override fun visit(commentStatement: CommentStatement): SMVExpr = SLiteral.TRUE
    override fun visit(blockStatement: BlockStatement): SMVExpr {
        blockStatement.statements.accept(this)
        return SLiteral.TRUE
    }
    //endregion

    override fun visit(special: SpecialStatement): SMVExpr {
        when (special) {
            is SpecialStatement.Assert -> {
                val name = special.name ?: "l${special.startPosition.lineNumber}"
                special.exprs.forEachIndexed { index, e ->
                    val def = ASSERTION_PREFIX + name + "_" + index
                    peek().auxiliaryDefinitions[SVariable.bool(def)] = e.accept(this)!!
                }
            }

            is SpecialStatement.Assume -> {
                val name = special.name ?: "l${special.startPosition.lineNumber}"
                special.exprs.forEachIndexed { index, e ->
                    val def = ASSUMPTION_PREFIX + name + "_" + index
                    peek().auxiliaryDefinitions[SVariable.bool(def)] = e.accept(this)!!
                }
            }
            is SpecialStatement.Havoc -> {
                val name = special.name ?: "l${special.startPosition.lineNumber}"
                special.variables.forEachIndexed { index, ref ->
                    val cnt = assignmentCounter.incrementAndGet()
                    val v = lift(ref)
                    val uniqueInput = SVariable(HAVOC_PREFIX + name + "_" + index, v.dataType!!)
                    peek().assign(v, cnt, uniqueInput)
                    peek().auxiliaryDefinitions[uniqueInput] = SLiteral.TRUE
                }
            }
        }

        return SLiteral.TRUE
    }

    //region Helper methods
    val lineNumberMap = LineMap()
    val assignmentCounter = AtomicInteger(-1)

    fun assign(vd: VariableDeclaration, value: SMVExpr) {
        val s = lift(vd)
        val cnt = assignmentCounter.incrementAndGet()

        vd.startPosition.run {
            lineNumberMap[cnt] = vd.toHuman() to this
        }
        peek().assign(s, cnt, value)
    }

    fun assign(ref: SymbolicReference, value: SMVExpr) {
        val s = lift(ref)
        val cnt = assignmentCounter.incrementAndGet()
        ref.startPosition.run {
            lineNumberMap[cnt] = ref.toHuman() to this
        }
        peek().assign(s, cnt, value)
    }

    fun SymbolicBranches.asCompressed(pos: Position): SymbolicState {
        val sb = SymbolicState(useDefinitions = useDefinitions)
        sb.auxiliaryDefinitions.putAll(auxiliary)
        variables.forEach { (t, u) ->
            val sv = sb.ensureVariable(t)
            val cnt = assignmentCounter.incrementAndGet()
            lineNumberMap[cnt] = t.name to pos
            val postfix = String.format("%s%05d", ASSIGN_SEPARATOR, cnt)
            sv.push(u.compress(), postfix)

            if (sv is SymbolicVariableTracing) {
                defines[t]?.let { sv.values.putAll(it) }
            }
            sb.variables[t] = sv
        }
        return sb
    }
    //endregion
}
