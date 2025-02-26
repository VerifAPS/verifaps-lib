package edu.kit.iti.formal.stvs.model.expressions

/**
 * Runtime-representation of unary expressions. Examples: <tt>NOT TRUE</tt>, <tt>- 3</tt>.
 * @param operation the unary operation
 * @param argument the expression to apply the operation to
 * @author Philipp
 */
data class UnaryFunctionExpr(val operation: Op, val argument: Expression) : Expression() {
    enum class Op {
        // BOOL -> BOOL
        NOT,

        // INT -> INT
        UNARY_MINUS,
    }

    override fun <R> accept(visitor: ExpressionVisitor<R>): R {
        return visitor.visitUnaryFunction(this)
    }
}
