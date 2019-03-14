package edu.kit.iti.formal.automation.il

import edu.kit.iti.formal.automation.operators.BinaryOperator
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.st.Cloneable
import edu.kit.iti.formal.automation.st.ast.*
import org.antlr.v4.runtime.ParserRuleContext
import java.io.Serializable


interface IlVisitable {
    fun <T> accept(visitor: IlVisitor<T>): T
}

interface IlVisitor<T> {
    fun visit(body: IlBody): T
    fun visit(simple: SimpleInstr): T
    fun visit(funCall: FunctionCallInstr): T
    fun visit(expr: ExprInstr): T
    fun visit(variable: IlOperand.Variable): T
    fun visit(constant: IlOperand.Constant): T
    fun visit(jump: JumpInstr): T
    fun visit(call: CallInstr): T
    abstract fun visit(param: IlParameter): T
    abstract fun visit(ret: RetInstr): T
}

abstract class IlBaseVisitor<T> : IlVisitor<T> {
    abstract fun defaultVisit(top: IlAst): T
    override fun visit(body: IlBody) = defaultVisit(body)
    override fun visit(simple: SimpleInstr) = defaultVisit(simple)
    override fun visit(funCall: FunctionCallInstr) = defaultVisit(funCall)
    override fun visit(expr: ExprInstr) = defaultVisit(expr)
    override fun visit(variable: IlOperand.Variable) = defaultVisit(variable)
    override fun visit(constant: IlOperand.Constant) = defaultVisit(constant)
    override fun visit(jump: JumpInstr) = defaultVisit(jump)
    override fun visit(ret: RetInstr) = defaultVisit(ret)
    override fun visit(call: CallInstr) = defaultVisit(call)
    override fun visit(param: IlParameter): T = defaultVisit(param)
}

class IlBaseVisitorN<T> : IlBaseVisitor<T?>() {
    override fun defaultVisit(top: IlAst): T? = null
}

abstract class IlTraversalVisitor : IlBaseVisitor<Unit>() {
    override fun visit(body: IlBody) {
        body.forEach { it.accept(this) }
    }

    override fun visit(simple: SimpleInstr) {
        simple.operand?.accept(this)
    }

    override fun visit(funCall: FunctionCallInstr) {
        funCall.operands.forEach { it.accept(this) }
    }

    override fun visit(expr: ExprInstr) {
        expr.operandi?.accept(this)
        expr.instr?.accept(this)
    }

    override fun visit(call: CallInstr) = call.parameters.forEach { it.accept(this) }
    override fun visit(param: IlParameter) = param.right.accept(this)
}


/**
 *
 * @author Alexander Weigl
 * @version 1 (20.02.19)
 */
sealed class IlAst : IlVisitable, Cloneable, Serializable, HasRuleContext {
    override var ruleContext: ParserRuleContext? = null
}

data class IlBody(private val seq: MutableList<IlInstr> = arrayListOf())
    : MutableList<IlInstr> by seq, IlAst() {
    override fun clone() = copy()
    override fun <T> accept(visitor: IlVisitor<T>): T = visitor.visit(this)
    fun findMarked(jump: String): IlInstr? {
        return find { it.labelled?.let { it == jump } ?: false }
    }

    fun posMarked(jump: String): Int? =
            findMarked(jump)?.let{ indexOf(it) }
}

abstract class IlInstr : IlAst() {
    var labelled: String? = null
    abstract override fun clone(): IlInstr
}

data class SimpleInstr(val type: SimpleOperand, val operand: IlOperand?) : IlInstr() {
    override fun <T> accept(visitor: IlVisitor<T>): T = visitor.visit(this)
    override fun clone() = copy()
}

sealed class IlOperand : IlAst() {
    abstract override fun clone(): IlOperand

    data class Variable(var ref: SymbolicReference) : IlOperand() {
        override fun <T> accept(visitor: IlVisitor<T>): T = visitor.visit(this)
        override fun clone(): IlOperand = copy()
    }

    data class Constant(var literal: Literal) : IlOperand() {
        override fun <T> accept(visitor: IlVisitor<T>): T = visitor.visit(this)
        override fun clone(): IlOperand = copy()
    }
}


data class ExprInstr(var operand: ExprOperand,
                     var operandi: IlOperand? = null,
                     var instr: IlBody?) : IlInstr() {
    override fun <T> accept(visitor: IlVisitor<T>): T = visitor.visit(this)
    override fun clone(): IlInstr = copy()
}

data class FunctionCallInstr(var function: SymbolicReference,
                             var operands: MutableList<IlOperand> = arrayListOf()) : IlInstr() {
    var invoked: Invoked? = null

    override fun <T> accept(visitor: IlVisitor<T>): T = visitor.visit(this)
    override fun clone(): IlInstr = copy()
}

/* expressed via CallInstr
data class FunctionBlockCall() : IlInstr() {
    override fun <T> accept(visitor: IlVisitor<T>): T = visitor.visit(this)
    override fun clone(): IlInstr = copy()
}
*/



data class JumpInstr(var type: JumpOperand, var target: String) : IlInstr() {
    override fun <T> accept(visitor: IlVisitor<T>): T = visitor.visit(this)
    override fun clone(): IlInstr = copy()
}


data class RetInstr(var type: ReturnOperand) : IlInstr() {
    override fun <T> accept(visitor: IlVisitor<T>): T = visitor.visit(this)
    override fun clone(): IlInstr = copy()
}

data class CallInstr(var type: CallOperand,
                     var ref: SymbolicReference,
                     var parameters: MutableList<IlParameter> = arrayListOf()) : IlInstr() {
    override fun <T> accept(visitor: IlVisitor<T>): T = visitor.visit(this)
    override fun clone(): IlInstr = copy()
}

data class IlParameter(val negated: Boolean = false, val input: Boolean = true,
                       val left: String = ANONYM, val right: IlOperand) : IlAst() {
    override fun <T> accept(visitor: IlVisitor<T>): T = visitor.visit(this)
    override fun clone() = copy(right = right.clone())
}


enum class CallOperand {
    CAL, CALC, CALCN, IMPLICIT_CALLED
}

enum class JumpOperand {
    JMP, JMPC, JMPCN
}

enum class ReturnOperand {
    RET, RETC, RETCN
}

enum class SimpleOperand(val symbol: String = "") {
    LD, LDN, ST, STN, STQ("ST?"), NOT, S, R, S1, R1, CLK, CU, CD, PV, IN, PT
}

enum class ExprOperand(val stOperator: BinaryOperator?, val altName: String? = null) {
    AND(Operators.AND, "&"), OR(Operators.OR), XOR(Operators.XOR), ANDN(null, "&N"),
    ORN(null), XORN(null), ADD(Operators.ADD), SUB(Operators.SUB), MUL(Operators.MULT),
    DIV(Operators.DIV), MOD(Operators.MOD), GT(Operators.GREATER_THAN), GE(Operators.GREATER_EQUALS),
    EQ(Operators.EQUALS), LT(Operators.LESS_THAN), LE(Operators.LESS_EQUALS), NE(Operators.NOT_EQUALS);
}