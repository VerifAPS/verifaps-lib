package edu.kit.iti.formal.stvs.model.expressions

/**
 * Runtime-representation of unary expressions. Examples: <tt>NOT TRUE</tt>, <tt>- 3</tt>.
 *
 * @author Philipp
 */
class UnaryFunctionExpr
/**
 * Creates an instance that represents an unary function.
 *
 * @param operation the unary operation
 * @param argument the expression to apply the operation to
 */(@JvmField val operation: Op?, @JvmField val argument: Expression?) : Expression() {
    enum class Op {
        // BOOL -> BOOL
        NOT,

        // INT -> INT
        UNARY_MINUS,
    }

    override fun <R> takeVisitor(visitor: ExpressionVisitor<R>): R? {
        return visitor.visitUnaryFunction(this)
    }

    override fun equals(o: Any?): Boolean {
        if (this === o) {
            return true
        }
        if (o !is UnaryFunctionExpr) {
            return false
        }

        val that = o

        if (operation != that.operation) {
            return false
        }
        return if (argument != null) argument == that.argument else that.argument == null
    }

    override fun hashCode(): Int {
        var result = operation?.hashCode() ?: 0
        result = 31 * result + (argument?.hashCode() ?: 0)
        return result
    }

    override fun toString(): String {
        return "Unary($operation $argument)"
    }
}
