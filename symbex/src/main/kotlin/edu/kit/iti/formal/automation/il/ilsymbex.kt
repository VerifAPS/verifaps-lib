package edu.kit.iti.formal.automation.il

import edu.kit.iti.formal.automation.SymbExFacade
import edu.kit.iti.formal.automation.rvt.SymbolicState
import edu.kit.iti.formal.automation.rvt.translators.DefaultTypeTranslator
import edu.kit.iti.formal.automation.rvt.translators.DefaultValueTranslator
import edu.kit.iti.formal.automation.rvt.translators.TypeTranslator
import edu.kit.iti.formal.automation.rvt.translators.ValueTranslator
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.DefaultInitValue
import edu.kit.iti.formal.automation.st.InitValueTranslator
import edu.kit.iti.formal.automation.st.ast.Invoked
import edu.kit.iti.formal.automation.st.ast.Literal
import edu.kit.iti.formal.automation.st.ast.SymbolicReference
import edu.kit.iti.formal.smv.SMVFacade
import edu.kit.iti.formal.smv.ast.*
import edu.kit.iti.formal.smv.joinToExpr
import java.util.concurrent.Callable
import java.util.concurrent.atomic.AtomicInteger

/**
 *
 * @author Alexander Weigl
 * @version 1 (21.02.19)
 */
class IlSymbex(ilBody: IlBody, maximalSteps: Int = 1000,
               scope: Scope,
               val state: SymbolicState = SymbolicState()) : Callable<SymbolicState> {
    private val context = IlSymbexContext(scope)

    fun initState() {
        context.scope.variables.forEach { vd ->
            val v = context.varCache.computeIfAbsent(vd.name) {
                SVariable(vd.name, context.typeTranslator.translate(vd.dataType!!))
            }
            state.assign(v, context.assignCounter.incrementAndGet(), v)
        }
    }

    init {
        context.onFork(Path(0, maximalSteps, ilBody, context, state = state))
    }

    override fun call(): SymbolicState {
        while (context.running.isNotEmpty()) {
            val p = context.running.first()
            context.running.remove(p)
            p.run()
        }
        if (context.terminated.size == 1) {
            return context.terminated.first().state
        } else {
            return SymbolicState().also { case ->
                for (vd in context.scope) {
                    val v = context.varCache[vd.name]!!
                    val states = context.terminated.map { path ->
                        val cond = path.pathCondition.joinToExpr(default = SLiteral.TRUE)
                        val expr = path.state[v] ?: v
                        cond to expr
                    }
                    val ve =
                            if (states.all { (a, b) -> b == states.first().second })
                                states.first().second
                            else {
                                SCaseExpression().also {
                                    states.forEach { (a, b) -> it.addCase(a, b) }
                                    it.addCase(SLiteral.TRUE, v)
                                }
                            }
                    case[v] = ve
                }
            }
        }
    }
}

internal class IlSymbexContext(val scope: Scope) {
    val assignCounter = AtomicInteger(-1)
    val running = arrayListOf<Path>()
    val terminated = arrayListOf<Path>()
    val errorVariable: SVariable = SVariable.bool("PATH_DIVERGED")
    val varCache = java.util.HashMap<String, SVariable>()
    //var operationMap: OperationMap = DefaultOperationMap()
    val typeTranslator: TypeTranslator = DefaultTypeTranslator()
    val valueTranslator: ValueTranslator = DefaultValueTranslator()
    var initValueTranslator: InitValueTranslator = DefaultInitValue

    fun onFinish(p: Path) {
        //p.pc = ilBody.size + 1
        terminated += p
    }

    fun onFork(p: Path) {
        running += p
    }

    fun translateToSmv(lit: Literal) =
            valueTranslator.translate(lit)

    fun translateToSmv(ref: SymbolicReference): SVariable =
            varCache.computeIfAbsent(ref.identifier) {
                typeTranslator.translate(scope.getVariable(ref))
            }

    fun translateToSmv(e: ExprOperand): SBinaryOperator = when (e) {
        ExprOperand.AND -> SBinaryOperator.AND
        ExprOperand.OR -> SBinaryOperator.OR
        ExprOperand.XOR -> SBinaryOperator.XOR
        ExprOperand.ANDN -> SBinaryOperator.AND
        ExprOperand.ORN -> SBinaryOperator.OR
        ExprOperand.XORN -> SBinaryOperator.XOR
        ExprOperand.ADD -> SBinaryOperator.PLUS
        ExprOperand.SUB -> SBinaryOperator.MINUS
        ExprOperand.MUL -> SBinaryOperator.MUL
        ExprOperand.DIV -> SBinaryOperator.DIV
        ExprOperand.MOD -> SBinaryOperator.MOD
        ExprOperand.GT -> SBinaryOperator.GREATER_THAN
        ExprOperand.GE -> SBinaryOperator.GREATER_EQUAL
        ExprOperand.EQ -> SBinaryOperator.EQUAL
        ExprOperand.LT -> SBinaryOperator.LESS_THAN
        ExprOperand.LE -> SBinaryOperator.LESS_EQUAL
        ExprOperand.NE -> SBinaryOperator.NOT_EQUAL
    }
}

internal data class Path(
        internal var currentIdx: Int = 0,
        private var remainingSteps: Int = 0,
        private val ilBody: IlBody,
        private val context: IlSymbexContext,
        private val subMode: Boolean = false,
        internal val state: SymbolicState = SymbolicState(),
        private var accumulator: SMVExpr = SLiteral.TRUE,
        internal var pathCondition: Set<SMVExpr> = hashSetOf()) : Runnable, IlTraversalVisitor() {
    private val remainingJumps = HashMap<Int, Int>()

    private val current: IlInstr
        get() = ilBody[currentIdx]

    private val ended: Boolean
        get() = //(current as? RetInstr).type == ReturnOperand.RET||
            currentIdx >= ilBody.size


    override fun run() {
        while (!ended && remainingSteps > 0) {
            //execute current state
            remainingSteps--
            current.accept(this)
        }
        if (!subMode) {
            if (currentIdx >= ilBody.size) {
                state.assign(context.errorVariable, context.assignCounter.incrementAndGet(), SLiteral.FALSE)
            } else
                if (remainingSteps <= 0) {
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

    //region instruction handling
    fun load(operand: IlOperand, N: Boolean = false) {
        val loadedValue =
                when (operand) {
                    is IlOperand.Variable ->
                        context.translateToSmv(operand.ref)
                    is IlOperand.Constant ->
                        context.translateToSmv(operand.literal)
                }
        val oldValue = accumulator

        if (N) {
            accumulator = SMVFacade.caseexpr(
                    oldValue.not(), loadedValue,
                    SLiteral.TRUE, oldValue)
        } else {
            accumulator = loadedValue
        }
    }

    fun store(operand: IlOperand, N: Boolean = false, test: Boolean = false) {
        if (test) TODO(" ?= is current not supported")
        if (operand is IlOperand.Constant) throw IllegalStateException("constant as storage target")
        val variable = context.translateToSmv((operand as IlOperand.Variable).ref)
        val varValue = if (N) {
            val oldValue = state[variable]!!
            SMVFacade.caseexpr(
                    accumulator.not(), SLiteral.FALSE,
                    SLiteral.TRUE, oldValue)
        } else {
            accumulator
        }
        state.assign(variable, context.assignCounter.incrementAndGet(), varValue)
    }

    fun not() {
        accumulator = accumulator.not()
    }

    fun reset(operand: IlOperand) {
        val ref = (operand as IlOperand.Variable).ref
        val variable = context.translateToSmv(ref)
        val oldValue = state[variable]!!
        val varValue =
                SMVFacade.caseexpr(
                        accumulator, SLiteral.FALSE,
                        SLiteral.TRUE, oldValue)
        state[variable] = varValue
    }

    fun set(operand: IlOperand) {
        val ref = (operand as IlOperand.Variable).ref
        val variable = context.translateToSmv(ref)
        val oldValue = state[variable]!!
        val varValue =
                SMVFacade.caseexpr(
                        accumulator, SLiteral.TRUE,
                        SLiteral.TRUE, oldValue)
        state[variable] = varValue
    }

    fun shortcall(type: SimpleOperand, operand: IlOperand) {
        //TODO Handle calls
        /*
        val func = (operand as IlOperand.Variable).ref
        val p = arrayListOf(InvocationParameter(type.name, false, accumulator))
        return InvocationStatement(func, p)
        */
    }

    fun makeCall(call: CallInstr, C: Boolean = false, N: Boolean = false) {
        //TODO Handle calls
        /*val args = call.parameters.map {
            val e = when (it.right) {
                is IlOperand.Variable -> it.right.ref
                is IlOperand.Constant -> it.right.literal
            }
            InvocationParameter(it.left, it.input, e)
        }.toMutableList()
        val invoke = InvocationStatement(call.ref, args)
        return when {
            N -> Statements.ifthen(accumulator.not(), invoke)
            C -> Statements.ifthen(accumulator, invoke)
            else -> invoke
        }
        */
    }
    //endregion

    //region visitor dispatching
    override fun defaultVisit(top: IlAst) {}

    override fun visit(ret: RetInstr) {
        val C = ret.type == ReturnOperand.RETC
        val N = ret.type == ReturnOperand.RETC

        if (C || N) {
            var cond = accumulator
            if (N) cond = cond.not()
            fork(cond, ilBody.size + 1)
        } else {
            currentIdx = ilBody.size + 1
        }
    }

    override fun visit(jump: JumpInstr) {
        val C = jump.type == JumpOperand.JMPC
        val N = jump.type == JumpOperand.JMPCN
        val pos = ilBody.posMarked(jump.target) ?: throw IllegalStateException("illegal jump position")

        if (C || N) { //TODO check the jump map
            var cond = accumulator
            if (N) cond = cond.not()
            fork(cond, pos)
            currentIdx++
        } else {
            currentIdx = pos
        }
    }

    override fun visit(simple: SimpleInstr) {
        when (simple.type) {
            SimpleOperand.NOT -> accumulator
            else ->
                when (simple.type) {
                    SimpleOperand.LD -> load(simple.operand!!)
                    SimpleOperand.LDN -> load(simple.operand!!, N = true)
                    SimpleOperand.ST -> store(simple.operand!!)
                    SimpleOperand.STN -> store(simple.operand!!, N = true)
                    SimpleOperand.STQ -> store(simple.operand!!, test = true)
                    SimpleOperand.S -> set(simple.operand!!)
                    SimpleOperand.R -> reset(simple.operand!!)
                    else -> shortcall(simple.type, simple.operand!!)
                }
        }
        currentIdx++
    }

    override fun visit(funCall: FunctionCallInstr) {
        val decl = (funCall.invoked as? Invoked.Function)
                ?: throw IllegalStateException("No function resolved for $funCall")

        val args = funCall.operands.map {
            when (it) {
                is IlOperand.Variable -> {
                    val ref = context.translateToSmv(it.ref) as SVariable
                    state[ref] ?: throw IllegalStateException("Variable not defined: $ref")
                }
                is IlOperand.Constant -> context.translateToSmv(it.literal)
            }
        }
        val ret = SymbExFacade.evaluateFunction(decl.function, args)
        accumulator = ret
        currentIdx++
    }

    override fun visit(expr: ExprInstr) {
        val sub = expr.instr ?: IlBody()
        expr.operandi?.also {
            //rewrite
            sub.add(0, SimpleInstr(SimpleOperand.LD, it))
            expr.operandi = null
        }
        val operator = context.translateToSmv(expr.operand)
        val left = accumulator
        val right: SMVExpr = exec(sub) //TODO Deal with side effects!
        accumulator = left.op(operator, right)
        if (expr.operand == ExprOperand.XORN ||
                expr.operand == ExprOperand.ORN ||
                expr.operand == ExprOperand.ANDN)
            accumulator = accumulator.not()
        currentIdx++
    }

    private fun exec(sub: IlBody): SMVExpr {
        val other = copy(0, subMode = true, ilBody = sub, pathCondition = hashSetOf())
        other.run()
        return other.accumulator
    }

    override fun visit(call: CallInstr) {
        when (call.type) {
            CallOperand.CAL -> makeCall(call)
            CallOperand.CALC -> makeCall(call, C = true)
            CallOperand.CALCN -> makeCall(call, N = true)
            CallOperand.IMPLICIT_CALLED -> makeCall(call)
        }
        currentIdx++
    }

    //endregion
}
