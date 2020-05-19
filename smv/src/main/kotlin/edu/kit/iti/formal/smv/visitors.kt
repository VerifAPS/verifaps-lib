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


abstract class SMVAstDefaultVisitorNN<T> : SMVAstVisitor<T> {
    protected abstract fun defaultVisit(top: SMVAst): T
    override fun visit(top: SMVAst): T = defaultVisit(top)
    override fun visit(v: SVariable): T = defaultVisit(v)
    override fun visit(be: SBinaryExpression): T = defaultVisit(be)
    override fun visit(ue: SUnaryExpression): T = defaultVisit(ue)
    override fun visit(l: SLiteral): T = defaultVisit(l)
    override fun visit(a: SAssignment): T = defaultVisit(a)
    override fun visit(ce: SCaseExpression): T = defaultVisit(ce)
    override fun visit(smvModule: SMVModule): T = defaultVisit(smvModule)
    override fun visit(func: SFunction): T = defaultVisit(func)
    override fun visit(quantified: SQuantified): T = defaultVisit(quantified)
}


open class SMVAstScanner : SMVAstVisitor<Unit> {
    override fun visit(top: SMVAst) = defaultVisit(top)
    override fun visit(v: SVariable) = defaultVisit(v)
    protected fun defaultVisit(ast: SMVAst) {}

    override fun visit(be: SBinaryExpression) {
        be.left.accept(this)
        be.right.accept(this)
    }

    override fun visit(ue: SUnaryExpression) {
        ue.expr.accept(this)
    }

    override fun visit(l: SLiteral) = defaultVisit(l)

    override fun visit(a: SAssignment) {
        a.expr.accept(this)
        a.target.accept(this)
    }

    override fun visit(ce: SCaseExpression) {
        for (c in ce.cases) {
            c.condition.accept(this)
            c.then.accept(this)
        }
    }

    override fun visit(smvModule: SMVModule) {
        smvModule.ctlSpec.forEach { it.accept(this) }
        smvModule.ltlSpec.forEach { it.accept(this) }
        smvModule.initAssignments.forEach { it.accept(this) }
        smvModule.initExpr.forEach { it.accept(this) }
        smvModule.definitions.forEach { it.accept(this) }
        smvModule.frozenVars.forEach { it.accept(this) }
        smvModule.inputVars.forEach { it.accept(this) }
        smvModule.stateVars.forEach { it.accept(this) }
        smvModule.invariantSpecs.forEach { it.accept(this) }
        smvModule.invariants.forEach { it.accept(this) }
        smvModule.moduleParameters.forEach { it.accept(this) }
        smvModule.nextAssignments.forEach { it.accept(this) }
        smvModule.transExpr.forEach { it.accept(this) }
    }

    override fun visit(func: SFunction) = defaultVisit(func)
    override fun visit(quantified: SQuantified) {
        quantified.quantified
                .forEach { it.accept(this) }

    }
}

/**
 */
abstract class SMVAstMutableVisitor : SMVAstVisitor<SMVAst> {
    override fun visit(top: SMVAst) = top
    override fun visit(v: SVariable): SMVExpr = v

    override fun visit(be: SBinaryExpression): SMVExpr {
        be.left = be.left.accept(this) as SMVExpr
        be.right = be.right.accept(this) as SMVExpr
        return be
    }

    override fun visit(ue: SUnaryExpression): SMVExpr {
        ue.expr = ue.expr.accept(this) as SMVExpr
        return ue
    }

    override fun visit(l: SLiteral): SMVExpr = l

    override fun visit(a: SAssignment): SAssignment {
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

    override fun visit(smvModule: SMVModule): SMVModule {
        smvModule.initAssignments = smvModule.initAssignments.visitAll()
        smvModule.nextAssignments = smvModule.nextAssignments.visitAll()
        smvModule.definitions = smvModule.definitions.visitAll()
        smvModule.ltlSpec = smvModule.ltlSpec.visitAll()
        smvModule.ctlSpec = smvModule.ctlSpec.visitAll()
        smvModule.frozenVars = smvModule.frozenVars.visitAll()
        smvModule.stateVars = smvModule.stateVars.visitAll()
        smvModule.inputVars = smvModule.inputVars.visitAll()
        smvModule.invariants = smvModule.invariants.visitAll()
        smvModule.moduleParameters = smvModule.moduleParameters.visitAll()
        return smvModule
    }

    override fun visit(func: SFunction): SMVExpr {
        return func
    }

    override fun visit(quantified: SQuantified): SMVExpr {
        quantified.quantified = quantified.quantified
                .map({ it.accept(this) as SMVExpr })
                .toMutableList()
        return quantified
    }

    private fun <E : SMVAst> List<E>.visitAll(): MutableList<E> =
            map { it.accept(this@SMVAstMutableVisitor) as E }.toMutableList()
}

class VariableReplacer(val map: Map<out SMVExpr, SMVExpr>) : SMVAstMutableVisitor() {
    override fun visit(v: SVariable): SMVExpr {
        return map.getOrDefault(v, v)
    }
}

open class ExpressionReplacer(protected val assignments: Map<out SMVExpr, SMVExpr>) : SMVAstMutableVisitor() {
    var changed = false
    protected open fun replace(x: SMVExpr): SMVExpr {
        val a = assignments[x]
        return if (a == null)
            super.visit(x) as SMVExpr
        else {
            changed = true;
            a
        }
    }

    override fun visit(v: SVariable): SMVExpr = replace(v)
    override fun visit(v: SBinaryExpression) = replace(v)
    override fun visit(v: SUnaryExpression) = replace(v)
    override fun visit(v: SLiteral) = replace(v)
    override fun visit(v: SFunction) = replace(v)
    override fun visit(v: SQuantified) = replace(v)
}

class SMVAstMutableTraversal(val visitor: SMVAstMutableVisitor) : SMVAstMutableVisitor() {
    override fun visit(top: SMVAst) = top
    override fun visit(v: SVariable): SMVExpr = v

    override fun visit(be: SBinaryExpression): SMVExpr {
        be.left = be.left.accept(visitor) as SMVExpr
        be.right = be.right.accept(visitor) as SMVExpr
        return be
    }

    override fun visit(ue: SUnaryExpression): SMVExpr {
        ue.expr = ue.expr.accept(visitor) as SMVExpr
        return ue
    }

    override fun visit(l: SLiteral): SMVExpr = l

    override fun visit(a: SAssignment): SAssignment {
        a.expr = a.expr.accept(visitor) as SMVExpr
        a.target = a.target.accept(visitor) as SVariable
        return a
    }

    override fun visit(ce: SCaseExpression): SMVExpr {
        for (c in ce.cases) {
            c.condition = c.condition.accept(visitor) as SMVExpr
            c.then = c.then.accept(visitor) as SMVExpr
        }
        return ce
    }

    /*override fun visit(smvModule: SMVModule): SMVModule {
        smvModule.initAssignments = smvModule.initAssignments.visitAll()
        smvModule.nextAssignments = smvModule.nextAssignments.visitAll()
        smvModule.definitions = smvModule.definitions.visitAll()
        smvModule.ltlSpec = smvModule.ltlSpec.visitAll()
        smvModule.ctlSpec = smvModule.ctlSpec.visitAll()
        smvModule.frozenVars = smvModule.frozenVars.visitAll()
        smvModule.stateVars = smvModule.stateVars.visitAll()
        smvModule.inputVars = smvModule.inputVars.visitAll()
        smvModule.invariants = smvModule.invariants.visitAll()
        smvModule.moduleParameters = smvModule.moduleParameters.visitAll()
        return smvModule
    }
*/
    override fun visit(func: SFunction): SMVExpr {
        func.arguments =
                func.arguments.map { it.accept(visitor) as SMVExpr }
                        .toMutableList()
        return func
    }

    override fun visit(quantified: SQuantified): SMVExpr {
        quantified.quantified = quantified.quantified
                .map { it.accept(visitor) as SMVExpr }
                .toMutableList()
        return quantified
    }
}

open class ExpressionReplacerRecur(val assignments: Map<out SMVExpr, SMVExpr>) : SMVAstMutableVisitor() {
    val traversal = SMVAstMutableTraversal(this)

    private var changed: Boolean = false

    protected fun replace(x: SMVExpr): SMVExpr {
        var a = x
        do {
            val nxt = assignments[a]
            if (nxt != null) a = nxt
            else break
        } while (true)

        changed = changed || a != x
        return a.accept(traversal) as SMVExpr
    }

    override fun visit(v: SVariable): SMVExpr = replace(v)
    override fun visit(v: SBinaryExpression): SMVExpr = replace(v) as SMVExpr
    override fun visit(v: SUnaryExpression): SMVExpr = (replace(v)) as SMVExpr
    override fun visit(v: SLiteral): SMVExpr = (replace(v)) as SMVExpr
    override fun visit(v: SFunction): SMVExpr = (replace(v)) as SMVExpr
    override fun visit(v: SQuantified): SMVExpr = (replace(v)) as SMVExpr
}