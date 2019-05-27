package edu.kit.iti.formal.automation.rvt

import com.ibm.dtfj.javacore.parser.j9.section.thread.ThreadPatternMatchers
import com.ibm.dtfj.javacore.parser.j9.section.thread.ThreadPatternMatchers.scope
import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.exceptions.*
import edu.kit.iti.formal.automation.il.*
import edu.kit.iti.formal.automation.il.Path
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.rvt.translators.*
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.DefaultInitValue
import edu.kit.iti.formal.automation.st.InitValueTranslator
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.ast.*
import java.lang.IllegalArgumentException
import java.util.*

/**
 * Created by weigl on 26.11.16.
 */
class StSymbolicExecutioner() {
    val context: StSymbexContext
    val scope: Scope

    constructor(exec: PouExecutable, maximalJumps: Int) : this() {
        context =
    }

    fun visit(programDeclaration: PouExecutable): SCaseExpression? {
        scope = programDeclaration.scope

        push(SymbolicState())

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

    fun start() {
        val state = SymbolicState.createInitialState(context::translateToSmv, ThreadPatternMatchers.scope)
        context.onFork(Path(0, maximalJumps, context, state = state))

        while (context.running.isNotEmpty()) {
            val path = context.running.removeAt(0)
            StSymbolicVisitor(path).run()
        }
    }
}

class SymbolicReturn : Throwable()
class SymbolicExit : Throwable()

open class StSymbolicVisitor(val path: StPath) : DefaultVisitor<SMVExpr>() {
    override fun defaultVisit(obj: Any) = throw IllegalStateException("Symbolic Executioner does not handle $obj")

    private val context = path.context

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
        return context.peek()[context.lift(symbolicReference)]
                ?: throw IllegalArgumentException()
    }

    override fun visit(invocation: Invocation): SMVExpr? {
        val fd = scope.resolveFunction(invocation) ?: throw FunctionUndefinedException(invocation)

        //initialize data structure
        val calleeState = SymbolicState(globalState)
        val callerState = peek()

        //region register function name as output variable
        try {
            fd.scope.getVariable(fd.name)
        } catch (e: VariableNotDefinedException) {
            val vd = VariableDeclaration(fd.name, VariableDeclaration.OUTPUT, fd.returnType.obj!!)
            vd.initValue = initValueTranslator.getInit(fd.returnType.obj!!)
            fd.scope.add(vd)
        }
        //endregion

        //region local variables (declaration and initialization)
        for (vd in fd.scope.variables) {
            //if (!calleeState.containsKey(vd.getName())) {
            val expr = this.valueTranslator.translate(vd.initValue!!)
            calleeState[lift(vd)] = expr
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
            val o = outputVars.find { it.name == parameter.name }
            val expr = parameter.expression
            if (o != null && parameter.expression is SymbolicReference) {
                val symVar = lift(expr as SymbolicReference)
                peek().replace(symVar, returnState[lift(o)]!!)
            }
            // TODO handle parameter.getExpression() instanceof Literal, etc.
        }

        //fd.getReturnType() != null
        return calleeState[fd.name]
    }

    override fun visit(literal: Literal): SLiteral {
        return this.valueTranslator.translate(literal)
    }
    //endregion

    //region ST Statements
    override fun visit(assign: AssignmentStatement): SMVExpr? {
        val s = context.peek()
        s[context.lift(assign.location as SymbolicReference)] = assign.expression.accept(this)!!
        return null
    }

    override fun visit(statements: StatementList): SCaseExpression? {
        for (s in statements) {
            if (s is ExitStatement || s is ReturnStatement) { //TODO throw exception to handle everything
                return null
            }
            s.accept(this)
        }
        return null
    }

    override fun visit(fbc: InvocationStatement): SMVExpr {
        when (fbc.invoked) {
            is Invoked.Program -> TODO()
            is Invoked.FunctionBlock -> TODO()
            is Invoked.Function -> TODO()
            is Invoked.Method -> TODO()
            is Invoked.Action -> TODO()
            null -> TODO()
        }
    }

    override fun visit(statement: IfStatement): SCaseExpression? {
        val branchStates = SymbolicBranches()

        for ((condition1, statements) in statement.conditionalBranches) {
            val condition = condition1.accept(this)!!
            context.push()
            statements.accept(this)
            branchStates.addBranch(condition, context.pop())
        }

        context.push()
        statement.elseBranch.accept(this)
        branchStates.addBranch(SLiteral.TRUE, context.pop())

        context.peek().putAll(branchStates.asCompressed())
        return null
    }

    override fun visit(caseStatement: CaseStatement): SMVExpr? {
        val branchStates = SymbolicBranches()
        for (gs in caseStatement.cases) {
            val condition = buildCondition(caseStatement.expression, gs)
            context.push()
            gs.statements.accept(this)
            branchStates.addBranch(condition, context.pop())
        }
        context.push()
        caseStatement.elseCase!!.accept(this)
        branchStates.addBranch(SLiteral.TRUE, context.pop())
        context.peek().putAll(branchStates.asCompressed())
        return null
    }

    override fun visit(whileStatement: WhileStatement): SMVExpr? {
        return super.visit(whileStatement)
    }

    override fun visit(repeatStatement: RepeatStatement): SMVExpr? {
        return super.visit(repeatStatement)
    }

    override fun visit(jump: JumpStatement): SMVExpr? {
        //FORK
        val C = jump.type == JumpOperand.JMPC
        val N = jump.type == JumpOperand.JMPCN
        val pos = stBody.posMarked(jump.target) ?: throw IllegalStateException("illegal jump position")

        if (C || N) { //TODO check the jump map
            var cond = accumulator
            if (N) cond = cond.not()
            fork(cond, pos)
            currentIdx++
        } else {
            currentIdx = pos
        }
    }

    override fun visit(exitStatement: ExitStatement): SMVExpr? = throw SymbolicExit()
    override fun visit(returnStatement: ReturnStatement): SMVExpr? = throw SymbolicReturn()
    //endregion

    //region case support
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
    //endregion

    //ignore
    override fun visit(commentStatement: CommentStatement) = null

    override fun visit(label: LabelStatement): SMVExpr? = null
}


class StSymbexContext {
    val running = arrayListOf<StPath>()
    val terminated = arrayListOf<StPath>()
    val errorVariable: SVariable = SVariable.bool("PATH_DIVERGED")
    val varCache = java.util.HashMap<String, SVariable>()
    val typeTranslator: TypeTranslator = DefaultTypeTranslator()
    val valueTranslator: ValueTranslator = DefaultValueTranslator()
    var initValueTranslator: InitValueTranslator = DefaultInitValue
    var operationMap: OperationMap = DefaultOperationMap()

    val state = Stack<SymbolicState>()
    var globalState = SymbolicState()
    var caseExpression: Expression? = null

    constructor(globalScope: Scope?) : this() {
        if (globalScope != null)
            scope = globalScope
    }

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
        var currentIdx: Int = 0,
        var remainingJumps: Int = 0,
        val stBody: StatementList,
        val context: StSymbexContext,
        val subMode: Boolean = false,
        val state: SymbolicState = SymbolicState(),
        var pathCondition: Set<SMVExpr> = hashSetOf()) : Runnable {

    private val ended: Boolean
        get() = //(current as? RetInstr).type == ReturnOperand.RET||
            currentIdx >= stBody.size


    override fun run() {
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

    private fun fork(cond: SMVExpr, forkedPC: Int) {
        val other = copy(
                currentIdx = forkedPC,
                state = SymbolicState(state), //TODO check for deep copy
                pathCondition = HashSet(pathCondition) + cond)
        pathCondition = pathCondition + cond.not()
        context.onFork(other)
    }
}
