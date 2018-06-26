package edu.kit.iti.formal.smv

import edu.kit.iti.formal.smv.ast.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (09.04.18)
 */

interface SMVAstVisitor<out T> {
    fun visit(top: SMVAst): T
    fun visit(v: SVariable): T
    fun visit(be: SBinaryExpression): T
    fun visit(ue: SUnaryExpression): T
    fun visit(l: SLiteral): T
    fun visit(a: SAssignment): T
    fun visit(ce: SCaseExpression): T
    fun visit(smvModule: SMVModule): T
    fun visit(func: SFunction): T
    fun visit(quantified: SQuantified): T
}

/**
 * @author Alexander Weigl
 * @version 1 (12.06.17)
 */
open class SMVAstDefaultVisitor<T> : SMVAstVisitor<T?> {
    protected open fun defaultVisit(top: SMVAst): T? = null
    override fun visit(top: SMVAst): T? = defaultVisit(top)
    override fun visit(v: SVariable): T? = defaultVisit(v)
    override fun visit(be: SBinaryExpression): T? = defaultVisit(be)
    override fun visit(ue: SUnaryExpression): T? = defaultVisit(ue)
    override fun visit(l: SLiteral): T? = defaultVisit(l)
    override fun visit(a: SAssignment): T? = defaultVisit(a)
    override fun visit(ce: SCaseExpression): T? = defaultVisit(ce)
    override fun visit(smvModule: SMVModule): T? = defaultVisit(smvModule)
    override fun visit(func: SFunction): T? = defaultVisit(func)
    override fun visit(quantified: SQuantified): T? = defaultVisit(quantified)
}

/**
 */
abstract class SMVAstMutableVisitor : SMVAstVisitor<SMVAst> {
    override fun visit(top: SMVAst) = top
    override fun visit(v: SVariable) = v

    override fun visit(be: SBinaryExpression): SMVExpr {
        be.left = be.left.accept(this) as SMVExpr
        be.right = be.right.accept(this) as SMVExpr
        return be
    }

    override fun visit(ue: SUnaryExpression): SMVExpr{
        ue.expr = ue.expr.accept(this) as SMVExpr
        return ue
    }

    override fun visit(l: SLiteral): SMVExpr= l

    override fun visit(a: SAssignment): SAssignment{
        a.expr = a.expr.accept(this) as SMVExpr
        a.target = a.target.accept(this) as SVariable
        return a
    }

    override fun visit(ce: SCaseExpression): SMVExpr {
        for (c in ce.cases) {
            c.condition = c.condition.accept(this) as SMVExpr
            c.then = c.then.accept(this) as SMVExpr
        }
        return ce
    }

    override fun visit(smvModule: SMVModule) = smvModule

    override fun visit(func: SFunction): SMVExpr {
        return func
    }

    override fun visit(quantified: SQuantified): SMVExpr {
        quantified.quantified = quantified.quantified
                .map({ it.accept(this) as SMVExpr })
                .toMutableList()
        return quantified
    }
}