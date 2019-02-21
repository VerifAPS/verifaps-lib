package edu.kit.iti.formal.automation.il

import edu.kit.iti.formal.automation.operators.BinaryOperator
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST
import edu.kit.iti.formal.automation.parser.IlParser
import edu.kit.iti.formal.automation.parser.IlParserBaseVisitor
import edu.kit.iti.formal.automation.st.ast.*
import org.antlr.v4.runtime.ParserRuleContext
import org.antlr.v4.runtime.Token

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

    override fun visitIlSimple(ctx: IlParser.IlSimpleContext)
            = SimpleInstr(SimpleOperand.valueOf(ctx.op.text),
            ctx.ilOperand().accept(this) as IlOperand)
            .also { it.ruleContext = ctx }

    override fun visitIlExpr(ctx: IlParser.IlExprContext) = ExprInstr(ExprOperand.valueOf(ctx.op.text),
            ctx.ilOperand()?.accept(this) as? IlOperand,
            ctx.ilSInstr()?.accept(this) as? IlBody)
            .also { it.ruleContext = ctx }

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


    private fun <T> allOf(ctx: List<ParserRuleContext>) =
            ctx.map { a -> a.accept(this) as T }
                    .toMutableList()

}