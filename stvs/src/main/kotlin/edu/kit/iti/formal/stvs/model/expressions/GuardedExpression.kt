package edu.kit.iti.formal.stvs.model.expressions

/**
 *
 * @author Alexander Weigl
 * @version 1 (21.04.24)
 */
data class GuardedExpression(
    val branches: List<Pair<Expression, Expression>>,
) : Expression() {
    override fun <R> accept(visitor: ExpressionVisitor<R>): R = visitor.visit(this)
}