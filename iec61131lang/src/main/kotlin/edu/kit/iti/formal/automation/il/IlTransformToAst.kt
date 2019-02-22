package edu.kit.iti.formal.automation.il

import edu.kit.iti.formal.automation.datatypes.AnyInt
import edu.kit.iti.formal.automation.datatypes.IECString
import edu.kit.iti.formal.automation.datatypes.values.DateAndTimeData
import edu.kit.iti.formal.automation.datatypes.values.DateData
import edu.kit.iti.formal.automation.datatypes.values.TimeData
import edu.kit.iti.formal.automation.datatypes.values.TimeofDayData
import edu.kit.iti.formal.automation.operators.BinaryOperator
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.parser.IlParser
import edu.kit.iti.formal.automation.parser.IlParserBaseVisitor
import edu.kit.iti.formal.automation.scope.TypeScope
import edu.kit.iti.formal.automation.sfclang.split
import edu.kit.iti.formal.automation.st.ast.*
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.Token
import java.math.BigInteger

/**
 *
 * @author Alexander Weigl
 * @version 1 (21.02.19)
 */
class IlTransformToAst : IlParserBaseVisitor<Any>() {
    override fun visitIlBody(ctx: IlParser.IlBodyContext): IlBody {
        val body = IlBody()
        ctx.ilInstruction().map { it.accept(this) }.forEach { body.add(it as IlInstr) }
        return body
    }

    override fun visitIlInstruction(ctx: IlParser.IlInstructionContext): IlInstr {
        val instr: IlInstr = ctx.ilInstr().accept(this) as IlInstr
        if (ctx.COLON() != null) {
            instr.labelled = ctx.IDENTIFIER()?.text
        }
        instr.ruleContext = ctx
        return instr
    }

    override fun visitIlInstr(ctx: IlParser.IlInstrContext) =
            oneOf(ctx.ilCall(), ctx.ilExpr(), ctx.ilFormalFunctionCall(), ctx.ilJump(), ctx.ilSimple(),
                    ctx.ilFunctionCall())!!


    override fun visitIlSInstr(ctx: IlParser.IlSInstrContext) =
            oneOf(ctx.ilExpr(), ctx.ilFormalFunctionCall(), ctx.ilSimple(), ctx.ilFunctionCall())!!


    private fun oneOf(vararg ctxs: ParserRuleContext?) =
            ctxs.find { it != null }?.accept(this)

    override fun visitIlSimple(ctx: IlParser.IlSimpleContext) = SimpleInstr(SimpleOperand.valueOf(ctx.op.text),
            ctx.ilOperand().accept(this) as IlOperand)
            .also { it.ruleContext = ctx }

    override fun visitIlExpr(ctx: IlParser.IlExprContext) = ExprInstr(ExprOperand.valueOf(ctx.op.text),
            ctx.ilOperand()?.accept(this) as? IlOperand,
            ctx.ilSInstrList()?.accept(this) as? IlBody)
            .also { it.ruleContext = ctx }

    override fun visitIlSInstrList(ctx: IlParser.IlSInstrListContext): IlBody {
        val body = IlBody()
        ctx.ilSInstr().forEach {
            body += it.accept(this) as IlInstr
        }
        return body
    }

    override fun visitIlFunctionCall(ctx: IlParser.IlFunctionCallContext) = FunctionCallInstr(ctx.symbolic_variable().accept(this) as SymbolicReference,
            ctx.ilOperand().map { it.accept(this) as IlOperand }.toMutableList())
            .also { it.ruleContext = ctx }

    override fun visitIlFormalFunctionCall(ctx: IlParser.IlFormalFunctionCallContext): CallInstr {
        return CallInstr(CallOperand.IMPLICIT_CALLED,
                ctx.symbolic_variable().accept(this) as SymbolicReference,
                ctx.param_assignment().map { it.accept(this) as IlParameter }.toMutableList())
                .also { it.ruleContext = ctx }
    }

    override fun visitIlJump(ctx: IlParser.IlJumpContext) = JumpInstr(JumpOperand.valueOf(ctx.op.text), ctx.label.text)
            .also { it.ruleContext = ctx }

    override fun visitIlCall(ctx: IlParser.IlCallContext): CallInstr {
        val callInstr = CallInstr(CallOperand.valueOf(ctx.op.text),
                ctx.symbolic_variable().accept(this) as SymbolicReference,
                ctx.param_assignment()
                        .map { it.accept(this) as IlParameter }.toMutableList())

        val seq = if (ctx.LPAREN() != null) {
            ctx.ilOperand()
                    .map { it.accept(this) as IlOperand }
                    .map { IlParameter(right = it) }
        } else {
            ctx.param_assignment().map { it.accept(this) as IlParameter }
        }
        callInstr.parameters = seq.toMutableList()

        return callInstr
    }

    override fun visitIlOperand(ctx: IlParser.IlOperandContext): Any {
        if (ctx.constant() != null) {
            val const = ctx.constant()!!.accept(this) as Literal
            return IlOperand.Constant(const).also { it.ruleContext = ctx.symbolic_variable() }
        }

        if (ctx.symbolic_variable() != null) {
            val a = ctx.symbolic_variable()
            val sr = a.accept(this) as SymbolicReference
            return IlOperand.Variable(sr).also { it.ruleContext = ctx.symbolic_variable() }
        }

        throw IllegalStateException()
    }

    override fun visitParam_assignment(ctx: IlParser.Param_assignmentContext): IlParameter {
        return IlParameter(negated = ctx.NOT() != null, input = ctx.ASSIGN() != null,
                left = ctx.id.text,
                right = if (ctx.ASSIGN() != null)
                    ctx.arg.accept(this) as IlOperand
                else
                    IlOperand.Variable(SymbolicReference(ctx.target.text))
        )

    }


    //copied
    override fun visitSymbolic_variable(ctx: IlParser.Symbolic_variableContext): Any {
        //TODO REWORK
        val ast = SymbolicReference()
        ast.ruleContext = ctx

        ast.identifier = ctx.a.text
        ast.sub = if (ctx.DOT() != null)
            ctx.other.accept(this) as SymbolicReference
        else
            null

        if (ctx.subscript_list() != null) {
            ast.subscripts = ctx.subscript_list().accept(this) as ExpressionList
        }

        ast.derefCount = ctx.deref.size

        return ast
    }

    override fun visitSubscript_list(
            ctx: IlParser.Subscript_listContext): ExpressionList {
        return ExpressionList(allOf<Expression>(ctx.expression()))
    }


    override fun visitUnaryNegateExpr(
            ctx: IlParser.UnaryNegateExprContext): Expression {
        val ast = UnaryExpression(Operators.NOT,
                ctx.sub.accept(this) as Expression)
        //Utils.setPosition(ast, ctx.NOT(), ctx.sub);
        ast.ruleContext = ctx
        return ast
    }

    override fun visitBinaryOrExpr(
            ctx: IlParser.BinaryOrExprContext): Any {
        val binaryExpr = binaryExpr(ctx.left, ctx.op, ctx.right)
        binaryExpr.ruleContext = (ctx)
        return binaryExpr
    }

    override fun visitBinaryCmpExpr(
            ctx: IlParser.BinaryCmpExprContext): Any {
        val expr = binaryExpr(ctx.left, ctx.op, ctx.right)
        expr.ruleContext = (ctx)
        return expr
    }

    override fun visitBinaryModDivExpr(
            ctx: IlParser.BinaryModDivExprContext): Any {
        val e = binaryExpr(ctx.left, ctx.op, ctx.right)
        e.ruleContext = (ctx)
        return e
    }

    override fun visitParenExpr(
            ctx: IlParser.ParenExprContext): Any {
        return ctx.expression().accept(this)
    }

    override fun visitBinaryXORExpr(
            ctx: IlParser.BinaryXORExprContext): Any {
        val e = binaryExpr(ctx.left, ctx.op, ctx.right)
        e.ruleContext = (ctx)
        return e
    }

    override fun visitUnaryMinusExpr(
            ctx: IlParser.UnaryMinusExprContext): Any {
        val ast = UnaryExpression(Operators.MINUS, ctx.sub.accept(this) as Expression)
        //Utils.setPosition(ast, ctx.NOT, ctx.sub.accept(this));
        ast.ruleContext = ctx
        return ast
    }

    override fun visitBinaryPowerExpr(
            ctx: IlParser.BinaryPowerExprContext): Any {
        val e = binaryExpr(ctx.left, ctx.op, ctx.right)
        e.ruleContext = (ctx)
        return e
    }

    override fun visitBinaryMultExpr(
            ctx: IlParser.BinaryMultExprContext): Any {
        val e = binaryExpr(ctx.left, ctx.op, ctx.right)
        e.ruleContext = (ctx)
        return e
    }

    override fun visitBinaryPlusMinusExpr(
            ctx: IlParser.BinaryPlusMinusExprContext): Any {
        val e = binaryExpr(ctx.left, ctx.op, ctx.right)
        e.ruleContext = (ctx)
        return e
    }

    override fun visitBinaryEqExpr(
            ctx: IlParser.BinaryEqExprContext): Any {
        val e = binaryExpr(ctx.left, ctx.op, ctx.right)
        e.ruleContext = (ctx)
        return e
    }

    override fun visitBinaryAndExpr(
            ctx: IlParser.BinaryAndExprContext): Any {
        val e = binaryExpr(ctx.left, ctx.op, ctx.right)
        e.ruleContext = (ctx)
        return e
    }

    fun binaryExpr(left: IlParser.ExpressionContext,
                   op: Token, right: IlParser.ExpressionContext): Expression {
        val binOp = Operators.lookup(op.text) as BinaryOperator
        return BinaryExpression(
                left.accept(this) as Expression,
                binOp,
                right.accept(this) as Expression)
    }

    override fun visitInvocation(ctx: IlParser.InvocationContext): Any {
        val i = Invocation()
        i.callee = ctx.id.accept(this) as SymbolicReference
        if (ctx.expression().isEmpty()) {
            // Using parameters
            i.addParameters(allOf(ctx.param_assignment()))
        } else {
            // Using expressions
            i.addExpressionParameters(allOf(ctx.expression()))
        }
        i.ruleContext = (ctx)
        return i
    }

    override fun visitCast(ctx: IlParser.CastContext): Literal {
        val (dt, _, v) = split(ctx.CAST_LITERAL().text)
        val ast = EnumLit(dt, v)
        //ast.originalToken = ctx.CAST_LITERAL().symbol
        ast.ruleContext = ctx
        return ast
    }

    private val tscope = TypeScope.builtin()

    override fun visitInteger(ctx: IlParser.IntegerContext): Any {
        val text = ctx.INTEGER_LITERAL().symbol
        val splitted = split(text.text)

        val dt = splitted.prefix
        val v = splitted.value
        val ordinal = splitted.ordinal ?: 10

        var int = BigInteger(v.replace("_", ""), ordinal)
        if (ctx.MINUS() != null)
            int *= -BigInteger.ONE
        val ast = IntegerLit(dt, int)
        try {
            //weigl: quick type for common integer type
            if (dt in tscope)
                ast.dataType.obj = tscope[dt] as AnyInt
        } catch (e: ClassCastException) {
        }
        ast.ruleContext = ctx
        return ast
    }

    override fun visitBits(ctx: IlParser.BitsContext): Any {
        val text = ctx.BITS_LITERAL().symbol
        val splitted = split(text.text)
        val dt = splitted.prefix
        val v = splitted.value
        if (v.equals("false", true))
            return BooleanLit(false)
        if (v.equals("true", true))
            return BooleanLit(true)


        val ordinal = splitted.ordinal ?: 10
        val ast = BitLit(dt, v.toLong(ordinal))
        ast.ruleContext = ctx
        return ast
    }

    override fun visitReal(ctx: IlParser.RealContext): Any {
        val (dt, _, v) = split(ctx.REAL_LITERAL().text)
        val ast = RealLit(dt, v.toBigDecimal())
        ast.ruleContext = ctx
        return ast
    }

    override fun visitString(ctx: IlParser.StringContext): Any {
        val ast = StringLit(
                if (ctx.STRING_LITERAL() != null) IECString.STRING
                else IECString.WSTRING,
                ctx.text)
        ast.ruleContext = ctx
        return ast
    }

    override fun visitTime(ctx: IlParser.TimeContext): Any {
        val ast = TimeLit(value = TimeData(ctx.text))
        ast.ruleContext = ctx
        return ast
    }

    override fun visitTimeofday(ctx: IlParser.TimeofdayContext): Any {
        val ast = ToDLit(value = TimeofDayData.parse(ctx.TOD_LITERAL().text!!))
        ast.ruleContext = ctx
        return ast
    }

    override fun visitDate(ctx: IlParser.DateContext): Any {
        val ast = DateLit(value = DateData.parse(ctx.DATE_LITERAL().text!!))
        ast.ruleContext = ctx
        return ast
    }

    override fun visitDatetime(ctx: IlParser.DatetimeContext): Any {
        val ast = DateAndTimeLit(value = DateAndTimeData.parse(ctx.DATETIME().text))
        ast.ruleContext = ctx
        return ast
    }

    override fun visitRef_null(ctx: IlParser.Ref_nullContext): Any {
        val ast = NullLit()
        ast.ruleContext = ctx
        return ast
    }

    override fun visitReference_value(ctx: IlParser.Reference_valueContext): Any {
        val ast = Invocation("ref")
        ast.addParameter(InvocationParameter(ctx.ref_to.accept(this) as SymbolicReference))
        return ast
    }


    private fun <T> allOf(ctx: List<ParserRuleContext>) =
            ctx.map { a -> a.accept(this) as T }
                    .toMutableList()

}