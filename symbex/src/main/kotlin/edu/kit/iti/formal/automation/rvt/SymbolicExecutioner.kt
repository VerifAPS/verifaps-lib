package edu.kit.iti.formal.automation.rvt

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.exceptions.*
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.rvt.translators.*
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.DefaultInitValue
import edu.kit.iti.formal.automation.st.InitValueTranslator
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitorNN
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.ast.SBinaryOperator
import edu.kit.iti.formal.smv.ast.SLiteral
import edu.kit.iti.formal.smv.ast.SMVExpr
import edu.kit.iti.formal.smv.ast.SVariable
import kotlin.collections.set

/**
 * Created by weigl on 26.11.16.
 */
class StSymbolicExecutioner(val scope: Scope, val stBody: StatementList, val maximalJumps: Int) {
    val context: StSymbexContext = StSymbexContext(scope, stBody)
    var startState = SymbolicState.createInitialState(context::lift, scope)

    constructor(exec: PouExecutable, maximalJumps: Int) : this(exec.scope, exec.stBody!!, maximalJumps)

    fun start(): SymbolicState {
        val path = StPath(maximalJumps, context, state = startState)
        val state = StSymbolicVisitor(path).run()
        println(state)
        return state
    }
}

class SymbolicReturn : Throwable()
class SymbolicExit : Throwable()
class AbortTrace : Throwable()

class StSymbolicExpression(val path: StPath) : DefaultVisitorNN<SMVExpr>() {
    val context = path.context
    val scope = path.context.scope

    override fun defaultVisit(obj: Any): SMVExpr {
        throw java.lang.IllegalArgumentException("Unhandled $obj : ${obj.javaClass}")
    }

    //region rewriting of expressions using the current state
    override fun visit(binaryExpression: BinaryExpression): SMVExpr {
        val left = binaryExpression.leftExpr.accept(this)!!
        val right = binaryExpression.rightExpr.accept(this)!!
        return context.operationMap.translateBinaryOperator(left, binaryExpression.operator, right)
    }

    override fun visit(u: UnaryExpression): SMVExpr {
        val left = u.expression.accept(this)!!
        return context.operationMap.translateUnaryOperator(u.operator, left)
    }

    override fun visit(symbolicReference: SymbolicReference): SMVExpr {
        return path.state[context.lift(symbolicReference)]
                ?: throw IllegalArgumentException()
    }

    override fun visit(invocation: Invocation): SMVExpr {
        val fd = scope.resolveFunction(invocation) ?: throw FunctionUndefinedException(invocation)

        //initialize data structure
        val calleeState = SymbolicState(path.globalState)
        val callerState = path.state

        //region register function name as output variable
        try {
            fd.scope.getVariable(fd.name)
        } catch (e: VariableNotDefinedException) {
            val vd = VariableDeclaration(fd.name, VariableDeclaration.OUTPUT, fd.returnType.obj!!)
            vd.initValue = context.initValueTranslator.getInit(fd.returnType.obj!!)
            fd.scope.add(vd)
        }
        //endregion

        //region local variables (declaration and initialization)
        for (vd in fd.scope.variables) {
            //if (!calleeState.containsKey(vd.getName())) {
            val expr = context.valueTranslator.translate(vd.initValue!!)
            calleeState[context.lift(vd)] = expr
            //}
        }
        //endregion

        //region transfer variables
        val parameters = invocation.parameters
        val inputVars = fd.scope.filterByFlags(
                VariableDeclaration.INPUT or VariableDeclaration.INOUT)

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
                calleeState[context.lift(inputVars[i])] = parameter.expression.accept(this)!!
            else {
                val o = inputVars.stream().filter { iv -> iv.name == parameter.name }.findAny()
                if (o.isPresent) {
                    val e = parameter.expression.accept(this)!!
                    calleeState[context.lift(o.get())] = e
                }
            }
        }

        for (outputVar in fd.scope.filterByFlags(VariableDeclaration.OUTPUT))
            calleeState[context.lift(outputVar)] = context.valueTranslator.translate(
                    context.initValueTranslator.getInit(outputVar.dataType!!))
        //push(calleeState)
        //endregion

        // execution of body
        val stBody = fd.stBody ?: throw IllegalArgumentException("Function ${fd.name} does not have an ST body.")
        val stSymbex = StSymbolicExecutioner(fd.scope, stBody, path.remainingJumps)
        val returnState = stSymbex.start()
        //val returnState = pop()

        // Update output variables
        val outputParameters = invocation.outputParameters
        val outputVars = fd.scope.filterByFlags(
                VariableDeclaration.OUTPUT, VariableDeclaration.INOUT)

        for (parameter in outputParameters) {
            val o = outputVars.find { it.name == parameter.name }
            val expr = parameter.expression
            if (o != null && parameter.expression is SymbolicReference) {
                val symVar = context.lift(expr as SymbolicReference)
                path.state.replace(symVar, returnState[context.lift(o)]!!)
            }
            // TODO handle parameter.getExpression() instanceof Literal, etc.
        }
        //fd.getReturnType() != null
        return calleeState[fd.name]!!
    }

    override fun visit(literal: Literal): SLiteral {
        return context.valueTranslator.translate(literal)
    }
    //endregion
}

open class StSymbolicVisitor(val path: StPath) : DefaultVisitorNN<Unit>() {
    val symbolicExpression = StSymbolicExpression(path)

    override fun defaultVisit(obj: Any) = throw IllegalStateException("Symbolic Executioner does not handle $obj")
    private val context = path.context

    fun run(): SymbolicState {
        val statements = path.remainingBody
        try {
            statements.accept(this)
        } catch (_: AbortTrace) {

        } catch (_: SymbolicReturn) {

        }
        return path.state
    }

    private fun runOnSide(statements: StatementList): SymbolicState {
        val path = StPath(path.remainingJumps, context, SymbolicState(path.state), 0)
        val s = StSymbolicVisitor(path)
        statements.accept(s)
        return path.state
    }

    //region ST Statements
    override fun visit(assign: AssignmentStatement) {
        path.state[context.lift(assign.location)] = assign.expression.accept(symbolicExpression)
    }

    override fun visit(statements: StatementList) {
        for (s in statements) {
            if (s is ExitStatement)
                throw SymbolicExit()

            if (s is ReturnStatement)
                throw SymbolicReturn()

            s.accept(this)
        }
    }

    override fun visit(fbc: InvocationStatement) {
        when (fbc.invoked) {
            is Invoked.Program -> TODO()
            is Invoked.FunctionBlock -> TODO()
            is Invoked.Function -> TODO()
            is Invoked.Method -> TODO()
            is Invoked.Action -> TODO()
            null -> TODO()
        }
    }

    override fun visit(statement: IfStatement) {
        val branchStates = SymbolicBranches()
        for ((condition1, statements) in statement.conditionalBranches) {
            val condition = condition1.accept(symbolicExpression)!!
            val s = runOnSide(statements)
            branchStates.addBranch(condition, s)
        }
        val elseState = runOnSide(statement.elseBranch)
        branchStates.addBranch(SLiteral.TRUE, elseState)
        path.state.putAll(branchStates.asCompressed())
    }

    override fun visit(caseStatement: CaseStatement) {
        val branchStates = SymbolicBranches()
        for (gs in caseStatement.cases) {
            val condition = buildCondition(caseStatement.expression, gs)
            val s = runOnSide(gs.statements)
            branchStates.addBranch(condition, s)
        }
        val elseState = runOnSide(caseStatement.elseCase!!)
        branchStates.addBranch(SLiteral.TRUE, elseState)
        path.state.putAll(branchStates.asCompressed())
    }

    override fun visit(jump: JumpStatement) {
        //FORK
        val pos = context.jumpMap[jump.target]
                ?: throw IllegalStateException("illegal jump position: ${jump.target}. Known positions ${context.jumpMap.keys}")
        --path.remainingJumps
        path.startIndex = pos
        StSymbolicVisitor(path).run()
        throw AbortTrace()
    }

    override fun visit(exitStatement: ExitStatement) = throw SymbolicExit()
    override fun visit(returnStatement: ReturnStatement) = throw SymbolicReturn()
    //endregion

    private fun buildCondition(e: Expression, c: Case): SMVExpr {
        val sceb = StCaseExpressionBuilder(e, symbolicExpression)
        return c.conditions
                .map { a -> a.accept(sceb) }
                .map { it }
                .reduce(SMVFacade.reducerKt(SBinaryOperator.OR))
    }

    //region ignore
    override fun visit(commentStatement: CommentStatement) {}

    override fun visit(label: LabelStatement) {}
    //endregion
}

class StCaseExpressionBuilder(val caseExpression: Expression,
                              val symbolicExpression: StSymbolicExpression) : DefaultVisitorNN<SMVExpr>() {
    override fun defaultVisit(obj: Any): SMVExpr {
        throw java.lang.IllegalArgumentException("Unhandled $obj : ${obj.javaClass} in ${javaClass}")
    }

    override fun visit(r: CaseCondition.Range): SMVExpr {
        val lower = BinaryExpression(caseExpression!!, Operators.GREATER_EQUALS, r.start!!)
        val upper = BinaryExpression(r.stop!!, Operators.GREATER_EQUALS, caseExpression!!)
        val and = BinaryExpression(lower, Operators.AND, upper)
        return and.accept(symbolicExpression)
    }

    override fun visit(i: CaseCondition.IntegerCondition): SMVExpr {
        val be = BinaryExpression(caseExpression!!, Operators.EQUALS, i.value)
        return be.accept(symbolicExpression)
    }

    override fun visit(e: CaseCondition.Enumeration): SMVExpr {
        val be = BinaryExpression(caseExpression!!, Operators.EQUALS, e.start)
        return be.accept(symbolicExpression)
    }

}

class StSymbexContext(val scope: Scope, val stBody: StatementList) {
    val running = arrayListOf<StPath>()
    val terminated = arrayListOf<StPath>()
    val errorVariable: SVariable = SVariable.bool("PATH_DIVERGED")
    val varCache = java.util.HashMap<String, SVariable>()
    val typeTranslator: TypeTranslator = DefaultTypeTranslator()
    val valueTranslator: ValueTranslator = DefaultValueTranslator()
    var initValueTranslator: InitValueTranslator = DefaultInitValue
    var operationMap: OperationMap = DefaultOperationMap()

    val jumpMap: MutableMap<String, Int> = createJumpMap(stBody)

    /*
        fun peek(): SymbolicState {
            return state.peek()
        }
        fun pop(): SymbolicState {
            return state.pop()
        }
        @JvmOverloads
        fun push(map: SymbolicState = SymbolicState(peek())) {
            state.push(map)
        }
    */

    fun lift(vd: VariableDeclaration): SVariable {
        try {
            return varCache.computeIfAbsent(vd.name) { this.typeTranslator.translate(vd) }
        } catch (e: NullPointerException) {
            throw UnknownDatatype("Datatype not given/inferred for variable $vd ${vd.dataType}", e)
        }

    }

    fun lift(vd: SymbolicReference): SVariable {
        return if (varCache.containsKey(vd.identifier))
            varCache[vd.identifier]!!
        else
            throw UnknownVariableException("Variable access to not declared variable: ${IEC61131Facade.print(vd)}. Line: ${vd.startPosition}")
    }

    fun onFinish(p: StPath) {
        //p.pc = ilBody.size + 1
        terminated += p
    }

    fun onFork(p: StPath) {
        running += p
    }

    fun translateToSmv(lit: Literal) =
            valueTranslator.translate(lit)

    fun translateToSmv(ref: SymbolicReference): SVariable =
            varCache.computeIfAbsent(ref.identifier) {
                typeTranslator.translate(scope.getVariable(ref))
            }
}

data class StPath(
        var remainingJumps: Int = 0,
        val context: StSymbexContext,
        val state: SymbolicState = SymbolicState(),
        var startIndex: Int = 0,
        var pathCondition: Set<SMVExpr> = hashSetOf()) {

    val globalState: SymbolicState
        get() {
            val gs = SymbolicState()
            context.scope.filterByFlags(VariableDeclaration.GLOBAL)
                    .map { context.lift(it) }
                    .forEach {
                        gs[it] = state[it]!! //maybe dangerous or?
                    }
            return gs
        }

    val stBody
        get() = context.stBody

    val remainingBody: StatementList
        get() {
            return if (startIndex >= stBody.size) {
                StatementList()
            } else {
                StatementList(stBody.subList(startIndex, stBody.size))
            }
        }


/*    override fun run() {
        while (!ended && remainingJumps > 0) {
            //execute current state
            remainingJumps--
            current.accept(this)
        }
        if (!subMode) {
            if (currentIdx >= stBody.size) {
                state[context.errorVariable] = SLiteral.FALSE
            } else
                if (remainingJumps <= 0) {
                    state[context.errorVariable] = SLiteral.TRUE
                }
            context.onFinish(this)
        }
    }

    /*private fun fork(forkedPC: Int) {
        val other = copy(
                currentIdx = forkedPC,
                state = SymbolicState(state), //TODO check for deep copy
                pathCondition = HashSet(pathCondition))

    }*/

 */
}

private fun createJumpMap(stBody: StatementList): MutableMap<String, Int> {
    val m = HashMap<String, Int>()
    stBody.forEachIndexed { index, statement ->
        if (statement is LabelStatement) {
            m[statement.label] = index
        }
    }
    return m
}