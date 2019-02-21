package edu.kit.iti.formal.automation.il

import edu.kit.iti.formal.automation.VariableScope
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.st.Statements
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.ast.BooleanLit.Companion.LFALSE
import edu.kit.iti.formal.automation.st.ast.BooleanLit.Companion.LTRUE
import java.util.concurrent.Callable

/**
 *
 * @author Alexander Weigl
 * @version 1 (21.02.19)
 */
class Il2St(val ilBody: IlBody) : Callable<Pair<VariableScope, StatementList>> {
    private val product = StatementList()
    private val scope = VariableScope()
    private val state: State = State()

    override fun call(): Pair<VariableScope, StatementList> {
        ilBody.accept(Impl())
        return scope to product
    }

    /**
     * Uses Table 68, from IEC61131-3 norm:
     *
     *
     *
     */

    /**
     * RET, RETC, RETN
     */
    fun ret(C: Boolean = false, N: Boolean = false) {
        product += when {
            N -> Statements.ifthen(
                    state.top.not(),
                    ReturnStatement())
            C -> Statements.ifthen(
                    state.top,
                    ReturnStatement())
            else -> ReturnStatement()
        }
    }

    /**
     * RET, RETC, RETN
     */
    fun jump(jump: String, C: Boolean = false, N: Boolean = false) {
        product += when {
            N -> Statements.ifthen(
                    state.top.not(),
                    ReturnStatement())
            C -> Statements.ifthen(
                    state.top,
                    ReturnStatement())
            else -> ReturnStatement()
        }
    }

    fun load(operand: IlOperand, N: Boolean = false) {
        if (N) TODO("Handle conditional case")
        when (operand) {
            is IlOperand.Variable -> state.push(operand.ref)
            is IlOperand.Constant -> state.push(operand.literal)
        }
    }

    fun store(operand: IlOperand, N: Boolean = false, test: Boolean = false) {
        val variable = operand as IlOperand.Variable
        if (N) {
            product += Statements.ifthen(state.top,
                    AssignmentStatement(variable.ref, BooleanLit.LTRUE)
                            .also { it.isAssignmentAttempt = test })
        } else {
            product += AssignmentStatement(variable.ref, state.top)
                    .also { it.isAssignmentAttempt = test }
        }
    }

    fun not() {
        state.push(state.top.not())
    }

    private fun reset(operand: IlOperand) {
        val ref = (operand as IlOperand.Variable).ref
        product += Statements.ifthen(state.top, AssignmentStatement(ref, LFALSE))
    }

    private fun set(operand: IlOperand) {
        val ref = (operand as IlOperand.Variable).ref
        product += Statements.ifthen(state.top, AssignmentStatement(ref, LTRUE))
    }

    private fun shortcall(type: SimpleOperand, operand: IlOperand) {
        val func = (operand as IlOperand.Variable).ref
        val p = arrayListOf(InvocationParameter(type.name, false, state.top))
        product += InvocationStatement(func, p)
    }

    inner class Impl : IlTraversalVisitor() {
        override fun defaultVisit(top: IlAst) {}
        override fun visit(ret: RetInstr) {
            when (ret.type) {
                ReturnOperand.RET -> ret()
                ReturnOperand.RETC -> ret(C = true)
                ReturnOperand.RETCN -> ret(N = true)
            }
        }

        override fun visit(j: JumpInstr) {
            when (j.type) {
                JumpOperand.JMP -> jump(j.target)
                JumpOperand.JMPC -> jump(j.target, C = true)
                JumpOperand.JMPCN -> jump(j.target, N = true)
            }
        }

        override fun visit(simple: SimpleInstr) {
            when (simple.type) {
                SimpleOperand.LD -> load(simple.operand!!)
                SimpleOperand.LDN -> load(simple.operand!!, N = true)
                SimpleOperand.ST -> store(simple.operand!!)
                SimpleOperand.STN -> store(simple.operand!!, N = true)
                SimpleOperand.STQ -> store(simple.operand!!, test = true)
                SimpleOperand.NOT -> not()
                SimpleOperand.S -> set(simple.operand!!)
                SimpleOperand.R -> reset(simple.operand!!)
                else /*
                SimpleOperand.S1 -> shortcall("S1")
                SimpleOperand.R1 -> ()
                SimpleOperand.CLK ->TODO()
                SimpleOperand.CU -> ()
                SimpleOperand.CD -> ODO()
                SimpleOperand.PV -> ()
                SimpleOperand.IN -> ()
                SimpleOperand.PT -> */ ->
                    shortcall(simple.type, simple.operand!!)
            }
        }

        override fun visit(funCall: FunctionCallInstr) {
            val inv = Invocation(funCall.function,
                    funCall.operands.map {
                        val e = when (it) {
                            is IlOperand.Variable -> it.ref
                            is IlOperand.Constant -> it.literal
                        }
                        InvocationParameter(e)
                    }.toMutableList())
            state.push(inv)
        }

        override fun visit(e: ExprInstr) {
            val binary = e.operand.stOperator
            val sub = e.instr ?: IlBody()
            e.operandi?.also {
                sub.add(0, SimpleInstr(SimpleOperand.LD, it))
            }
            val left = state.top
            sub.accept(Impl())
            val right = state.top
            if (binary != null) {
                state.push(BinaryExpression(left, binary, right))
            } else {
                when (e.operand) {
                    ExprOperand.XORN ->
                        state.push(BinaryExpression(left, Operators.XOR, right).not())
                    ExprOperand.ORN ->
                        state.push(left.or(right).not())
                    ExprOperand.ANDN ->
                        state.push(left.and(right).not())
                    else -> throw IllegalStateException()
                }
            }
        }

        override fun visit(call: CallInstr) {
            when (call.type) {
                CallOperand.CAL -> makeCall(call)
                CallOperand.CALC -> makeCall(call, C = true)
                CallOperand.CALCN -> makeCall(call, N = true)
                CallOperand.IMPLICIT_CALLED -> makeCall(call)
            }
        }
    }

    private fun makeCall(call: CallInstr, C: Boolean = false, N: Boolean = false) {
        val args = call.parameters.map {
            val e = when (it.right) {
                is IlOperand.Variable -> it.right.ref
                is IlOperand.Constant -> it.right.literal
            }
            InvocationParameter(it.left, it.input, e)
        }.toMutableList()
        val invoke = InvocationStatement(call.ref, args)
        product += when {
            N -> Statements.ifthen(state.top.not(), invoke)
            C -> Statements.ifthen(state.top, invoke)
            else -> invoke
        }
    }
}

internal class State {
    fun push(ref: Expression) {
        stack += ref
    }

    val stack = arrayListOf<Expression>()
    val locals = hashMapOf<String, Expression>()
    val top: Expression
        get() = stack.last()
}