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
    val unwinding: Boolean = false
    private var currentPos: Int = 0
    private val product = StatementList()
    private val scope = VariableScope()
    private val accumulator: Accumulator = Accumulator()
    private var factory = IlStatementFactory(accumulator)
    private val marks = HashMap<String, Statement>()

    override fun call(): Pair<VariableScope, StatementList> {
        ilBody.accept(Impl())
        return scope to product
    }

    /**
     * JMP{C,N}
     */
    fun jump(jump: String, C: Boolean = false, N: Boolean = false): Statement {
        //val pos = ilBody.posMarked(jump)
        return when {
            N -> Statements.ifthen(
                    accumulator.top.not(),
                    JumpStatement(jump))
            C -> Statements.ifthen(
                    accumulator.top,
                    JumpStatement(jump))
            else -> JumpStatement(jump)
        }
    }

    inner class Impl : IlTraversalVisitor() {
        override fun defaultVisit(top: IlAst) {}
        override fun visit(ret: RetInstr) {
            label(ret)
            append(when (ret.type) {
                ReturnOperand.RET -> factory.ret()
                ReturnOperand.RETC -> factory.ret(C = true)
                ReturnOperand.RETCN -> factory.ret(N = true)
            })
        }

        override fun visit(j: JumpInstr) {
            label(j)
            append(when (j.type) {
                JumpOperand.JMP -> jump(j.target)
                JumpOperand.JMPC -> jump(j.target, C = true)
                JumpOperand.JMPCN -> jump(j.target, N = true)
            })
        }

        override fun visit(simple: SimpleInstr) {
            label(simple)
            when (simple.type) {
                SimpleOperand.NOT -> factory.not()
                SimpleOperand.LD -> factory.load(simple.operand!!)
                SimpleOperand.LDN -> factory.load(simple.operand!!, N = true)
                else ->
                    append(
                            when (simple.type) {
                                SimpleOperand.ST -> factory.store(simple.operand!!)
                                SimpleOperand.STN -> factory.store(simple.operand!!, N = true)
                                SimpleOperand.STQ -> factory.store(simple.operand!!, test = true)
                                SimpleOperand.S -> factory.set(simple.operand!!)
                                SimpleOperand.R -> factory.reset(simple.operand!!)
                                else /*
                SimpleOperand.S1 -> shortcall("S1")
                SimpleOperand.R1 -> ()
                SimpleOperand.CLK ->TODO()
                SimpleOperand.CU -> ()
                SimpleOperand.CD -> ODO()
                SimpleOperand.PV -> ()
                SimpleOperand.IN -> ()
                SimpleOperand.PT -> */ ->
                                    factory.shortcall(simple.type, simple.operand!!)
                            }
                    )
            }
        }

        private fun append(any: Statement) {
            product.add(any)
        }

        override fun visit(funCall: FunctionCallInstr) {
            label(funCall)
            val inv = Invocation(funCall.function,
                    funCall.operands.map {
                        val e = when (it) {
                            is IlOperand.Variable -> it.ref
                            is IlOperand.Constant -> it.literal
                        }
                        InvocationParameter(e)
                    }.toMutableList())
            accumulator.push(inv)
        }

        override fun visit(e: ExprInstr) {
            label(e)

            val binary = e.operand.stOperator
            val sub = e.instr ?: IlBody()
            e.operandi?.also {
                sub.add(0, SimpleInstr(SimpleOperand.LD, it))
            }
            val left = accumulator.top
            sub.accept(Impl())
            val right = accumulator.top
            if (binary != null) {
                accumulator.push(BinaryExpression(left, binary, right))
            } else {
                when (e.operand) {
                    ExprOperand.XORN ->
                        accumulator.push(BinaryExpression(left, Operators.XOR, right).not())
                    ExprOperand.ORN ->
                        accumulator.push(left.or(right).not())
                    ExprOperand.ANDN ->
                        accumulator.push(left.and(right).not())
                    else -> throw IllegalStateException()
                }
            }
        }

        override fun visit(call: CallInstr) {
            label(call)
            when (call.type) {
                CallOperand.CAL -> factory.makeCall(call)
                CallOperand.CALC -> factory.makeCall(call, C = true)
                CallOperand.CALCN -> factory.makeCall(call, N = true)
                CallOperand.IMPLICIT_CALLED -> factory.makeCall(call)
            }
        }

        private fun label(instr: IlInstr) {
            instr.labelled?.also {
                append(LabelStatement(it))
            }
        }
    }
}

/**
 * Uses Table 68, from IEC61131-3 norm:
 *
 *
 *
 */
class IlStatementFactory(val accumulator: Accumulator) {
    /**
     * RET, RETC, RETN
     */
    fun ret(C: Boolean = false, N: Boolean = false): Statement {
        return when {
            N -> Statements.ifthen(
                    accumulator.top.not(),
                    ReturnStatement())
            C -> Statements.ifthen(
                    accumulator.top,
                    ReturnStatement())
            else -> ReturnStatement()
        }
    }

    fun load(operand: IlOperand, N: Boolean = false) {
        if (N) TODO("Handle conditional case")
        return when (operand) {
            is IlOperand.Variable -> accumulator.push(operand.ref)
            is IlOperand.Constant -> accumulator.push(operand.literal)
        }
    }

    fun store(operand: IlOperand, N: Boolean = false, test: Boolean = false): Statement {
        val variable = operand as IlOperand.Variable
        return if (N) {
            Statements.ifthen(accumulator.top,
                    AssignmentStatement(variable.ref, BooleanLit.LTRUE)
                            .also { it.isAssignmentAttempt = test })
        } else {
            AssignmentStatement(variable.ref, accumulator.top)
                    .also { it.isAssignmentAttempt = test }
        }
    }

    fun not() {
        accumulator.push(accumulator.top.not())
    }

    fun reset(operand: IlOperand): Statement {
        val ref = (operand as IlOperand.Variable).ref
        return Statements.ifthen(accumulator.top, AssignmentStatement(ref, LFALSE))
    }

    fun set(operand: IlOperand): Statement {
        val ref = (operand as IlOperand.Variable).ref
        return Statements.ifthen(accumulator.top, AssignmentStatement(ref, LTRUE))
    }

    fun shortcall(type: SimpleOperand, operand: IlOperand): Statement {
        val func = (operand as IlOperand.Variable).ref
        val p = arrayListOf(InvocationParameter(type.name, false, accumulator.top))
        return InvocationStatement(func, p)
    }

    fun makeCall(call: CallInstr, C: Boolean = false, N: Boolean = false): Statement {
        val args = call.parameters.map {
            val e = when (it.right) {
                is IlOperand.Variable -> it.right.ref
                is IlOperand.Constant -> it.right.literal
            }
            InvocationParameter(it.left, it.input, e)
        }.toMutableList()
        val invoke = InvocationStatement(call.ref, args)
        return when {
            N -> Statements.ifthen(accumulator.top.not(), invoke)
            C -> Statements.ifthen(accumulator.top, invoke)
            else -> invoke
        }
    }
}

class Accumulator {
    fun push(ref: Expression) {
        stack += ref
    }

    val stack = arrayListOf<Expression>()
    val top: Expression
        get() = stack.last()

    operator fun invoke() = top
}