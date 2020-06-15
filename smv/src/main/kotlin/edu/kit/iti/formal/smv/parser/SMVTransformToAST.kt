package edu.kit.iti.formal.smv.parser

/*-
 * #%L
 * smv-model
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.smv.*
import edu.kit.iti.formal.smv.ast.*
import java.math.BigDecimal
import java.math.BigInteger
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (10.06.17)
 */
class SMVTransformToAST : SMVBaseVisitor<Any>() {
    private var lastModule: SMVModule? = null

    override fun visitExprEOF(ctx: SMVParser.ExprEOFContext) = ctx.expr().accept(this)

    override fun visitModules(ctx: SMVParser.ModulesContext): List<SMVModule> {
        val moduleDeclarations = ArrayList<SMVModule>()
        ctx.module().forEach { c -> moduleDeclarations.add(c.accept(this) as SMVModule) }
        return moduleDeclarations
    }

    override fun visitModule(ctx: SMVParser.ModuleContext): SMVModule {
        val module = SMVModule(ctx.name.text)
        ctx.params.forEach { fpctx ->
            module.moduleParameters.add(
                    SVariable.create(fpctx.getText()).with(null))
        }

        lastModule = module
        ctx.moduleElement().forEach { c -> c.accept(this) }
        return module
    }

    override fun visitModuleElement(ctx: SMVParser.ModuleElementContext): Any? {
        println(ctx.childCount)
        println(ctx.getChild(0))
        return ctx.getChild(0).accept(this)
    }

    override fun visitVariableDeclaration(ctx: SMVParser.VariableDeclarationContext): Any {
        ctx.varBody().forEach { varBody ->
            lastModule!!.stateVars.add(
                    varBody.accept(this) as SVariable)
        }
        return lastModule!!.stateVars
    }

    override fun visitIVariableDeclaration(ctx: SMVParser.IVariableDeclarationContext): Any {
        ctx.varBody().forEach { varBody ->
            lastModule!!.inputVars.add(
                    varBody.accept(this) as SVariable)
        }
        return lastModule!!.stateVars
    }

    override fun visitFrozenVariableDeclaration(ctx: SMVParser.FrozenVariableDeclarationContext): Any {
        ctx.varBody().forEach { varBody ->
            lastModule!!.frozenVars.add(
                    varBody.accept(this) as SVariable)
        }
        return lastModule!!.stateVars
    }

    override fun visitVarBody(ctx: SMVParser.VarBodyContext): SVariable {
        val sVariable = SVariable(ctx.name.text)
        sVariable.dataType = (ctx.type().accept(this) as SMVType)
        return sVariable
    }

    override fun visitDefineBody(ctx: SMVParser.DefineBodyContext): Any? {
        lastModule!!.definitions.add(
                SAssignment(SVariable.create(ctx.`var`.getText()).with(null),
                        ctx.expr().accept(this) as SMVExpr))
        return null
    }

    override fun visitConstantsDeclaration(ctx: SMVParser.ConstantsDeclarationContext): Any {
        throw IllegalStateException("not supported")
    }

    override fun visitVarBodyAssign(ctx: SMVParser.VarBodyAssignContext): Any {
        return super.visitVarBodyAssign(ctx)
    }

    override fun visitInitBody(ctx: SMVParser.InitBodyContext): Any? {
        lastModule!!.initAssignments.add(
                SAssignment(
                        SVariable.create(ctx.`var`.getText()).with(null),
                        ctx.expr().accept(this) as SMVExpr
                ))
        return null
    }

    override fun visitNextBody(ctx: SMVParser.NextBodyContext): Any? {
        lastModule!!.nextAssignments.add(
                SAssignment(
                        SVariable.create(ctx.`var`.getText()).with(null),
                        ctx.expr().accept(this) as SMVExpr
                ))
        return null
    }

    override fun visitFairnessConstraint(ctx: SMVParser.FairnessConstraintContext): Any {
        return super.visitFairnessConstraint(ctx)
    }

    override fun visitPslSpecification(ctx: SMVParser.PslSpecificationContext): Any {
        return super.visitPslSpecification(ctx)
    }

    override fun visitInvarSpecification(ctx: SMVParser.InvarSpecificationContext): Any? {
        lastModule!!.invariantSpecs.add(
                ctx.expr().accept(this) as SMVExpr
        )
        return null
    }

    override fun visitCtlSpecification(ctx: SMVParser.CtlSpecificationContext): Any? {
        lastModule!!.ctlSpec.add(
                ctx.expr().accept(this) as SMVExpr
        )
        return null
    }

    override fun visitIsaDeclaration(ctx: SMVParser.IsaDeclarationContext): Any {
        return super.visitIsaDeclaration(ctx)
    }

    override fun visitLtlSpecification(ctx: SMVParser.LtlSpecificationContext): Any? {
        lastModule!!.ltlSpec.add(ctx.expr().accept(this) as SMVExpr)
        return null
    }


    override fun visitType(ctx: SMVParser.TypeContext): SMVType {
        return if (ctx.moduleType() != null) {
            ctx.moduleType().accept(this) as SMVType
        } else {
            ctx.simpleType().accept(this) as SMVType
        }
    }

    override fun visitBooleanType(ctx: SMVParser.BooleanTypeContext): SMVType {
        return SMVTypes.BOOLEAN
    }

    override fun visitWordType(ctx: SMVParser.WordTypeContext): Any {
        return super.visitWordType(ctx)
    }

    override fun visitSignedType(ctx: SMVParser.SignedTypeContext): Any {
        return SMVWordType(true,
                Integer.parseInt(ctx.bits.getText()))
    }

    override fun visitUnsignedType(ctx: SMVParser.UnsignedTypeContext): Any {
        return SMVWordType(false,
                Integer.parseInt(ctx.bits.getText()))
    }

    override fun visitEnumType(ctx: SMVParser.EnumTypeContext): Any {
        val ids = ctx.expr().map { it.getText() }
        return EnumType(ids)
    }

    override fun visitIntervalType(ctx: SMVParser.IntervalTypeContext): Any {
        throw IllegalStateException("not supported")
        //        return super.visitIntervalType(ctx);
    }

    override fun visitArrayType(ctx: SMVParser.ArrayTypeContext): Any {
        throw IllegalStateException("not supported")
        //  return super.visitArrayType(ctx);
    }

    override fun visitModuleTypeSimple(ctx: SMVParser.ModuleTypeSimpleContext): Any {
        val parameters: List<SMVExpr> = ctx.stateExpr()
                .map({ se -> se.accept(this) as SMVExpr })
        return ModuleType(ctx.mod.text, parameters)
    }

    override fun visitStateExpr(ctx: SMVParser.StateExprContext): SMVExpr {
        if (ctx.unaryop != null) {
            return SUnaryExpression(
                    if (ctx.unaryop.getText().equals("!"))
                        SUnaryOperator.NEGATE
                    else
                        SUnaryOperator.MINUS,
                    ctx.stateExpr(0).accept(this) as SMVExpr
            )
        }

        return if (ctx.terminalAtom() != null) {
            ctx.terminalAtom().accept(this) as SMVExpr
        } else SBinaryExpression(
                ctx.stateExpr(0).accept(this) as SMVExpr,
                SBinaryOperator.findBySymbol(ctx.op.getText())!!,
                ctx.stateExpr(1).accept(this) as SMVExpr
        )

    }

    override fun visitParen(ctx: SMVParser.ParenContext): SMVExpr {
        return ctx.stateExpr().accept(this) as SMVExpr
    }

    override fun visitSetExpr(ctx: SMVParser.SetExprContext): Any {
        throw IllegalStateException("not supported")
        //        return super.visitSetExpr(ctx);
    }

    override fun visitWordValue(ctx: SMVParser.WordValueContext): Any {
        val p = ctx.text.split("_")
        val gdt = p[0][1] == 's'

        val bits = Integer.parseInt(p[0].substring(3))
        return SWordLiteral(BigInteger(p[1]), SMVWordType(gdt, bits))
    }

    override fun visitRangeExpr(ctx: SMVParser.RangeExprContext): Any {
        throw IllegalStateException("not supported")
        //return super.visitRangeExpr(ctx);
    }

    override fun visitCasesExpr(ctx: SMVParser.CasesExprContext): Any {
        val e = SCaseExpression()
        for (a in ctx.caseBranch()) {
            val cond = a.cond.accept(this) as SMVExpr
            val `val` = a.`val`.accept(this) as SMVExpr
            e.add(cond, `val`)
        }
        return e
    }


    override fun visitTrueExpr(ctx: SMVParser.TrueExprContext): SLiteral {
        return SLiteral.TRUE
    }

    override fun visitFalseExpr(ctx: SMVParser.FalseExprContext): SLiteral {
        return SLiteral.FALSE
    }

    override fun visitModuleTypeProcess(ctx: SMVParser.ModuleTypeProcessContext): Any {
        throw IllegalStateException("not supported")
    }

    override fun visitTemporalBinExpr(ctx: SMVParser.TemporalBinExprContext): Any {
        return SQuantified(STemporalOperator.valueOf(ctx.op),
                ctx.left.accept(this) as SMVExpr,
                ctx.right.accept(this) as SMVExpr)
    }

    override fun visitTemporalUnaryExpr(ctx: SMVParser.TemporalUnaryExprContext): Any {
        return SQuantified(
                STemporalOperator.valueOf(ctx.op),
                ctx.expr().accept(this) as SMVExpr
        )
    }

    override fun visitTemporalParen(ctx: SMVParser.TemporalParenContext): SMVExpr {
        return ctx.expr().accept(this) as SMVExpr
    }

    override fun visitFunctionExpr(ctx: SMVParser.FunctionExprContext): SMVExpr {
        val exprs = getSMVExprs(ctx)
        return SFunction(ctx.func.text, exprs)
    }

    private fun getSMVExprs(ctx: SMVParser.FunctionExprContext): List<SMVExpr> {
        return ctx.stateExpr().map { it.accept(this) as SMVExpr }
    }

    override fun visitCasesExprAtom(ctx: SMVParser.CasesExprAtomContext): Any {
        return super.visitCasesExprAtom(ctx)
    }

    override fun visitVariableAccess(ctx: SMVParser.VariableAccessContext): Any {
        return SVariable.create(ctx.getText()).with(null)
    }

    override fun visitArrayAccess(ctx: SMVParser.ArrayAccessContext): Any {
        throw IllegalStateException("not supported")
    }

    override fun visitVariableDotted(ctx: SMVParser.VariableDottedContext): Any {
        throw IllegalStateException("not supported")
    }

    override fun visitIntegerLiteral(ctx: SMVParser.IntegerLiteralContext): Any {
        return SIntegerLiteral(BigInteger(ctx.value.getText()))
    }

    override fun visitFloatLiteral(ctx: SMVParser.FloatLiteralContext): Any {
        return SFloatLiteral(BigDecimal(ctx.value.getText()))
    }

    override fun visitCaseBranch(ctx: SMVParser.CaseBranchContext): Any {
        return super.visitCaseBranch(ctx)
    }
}