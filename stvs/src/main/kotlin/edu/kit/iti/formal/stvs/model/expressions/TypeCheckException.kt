package edu.kit.iti.formal.stvs.model.expressions

/**
 * An Exception for type errors. Occurs when one wants to parse an [Expression] like
 * <tt>2 AND TRUE</tt> or <tt>42 = FALSE</tt>.
 *
 * @author Philipp
 */
class TypeCheckException
/**
 * Create a new TypeCheckException.
 * @param mistypedExpression the expression that is ill-typed. This would be the whole expression
 * (for example <tt>2 AND TRUE</tt>)
 * @param message a message about what went wrong.
 */(
    /**
     * Get the expression for which this TypeCheckException was thrown.
     * @return the expression that is ill-typed. This would be the whole expression (for example
     * <tt>2 AND TRUE</tt>)
     */
    val mistypedExpression: Expression?, message: String?
) : Exception(
    "$message\nIn Expression: $mistypedExpression"
) {
    override fun hashCode(): Int {
        return if (mistypedExpression != null) mistypedExpression.hashCode() else 0
    }

    override fun equals(o: Any?): Boolean {
        if (this === o) {
            return true
        }
        if (o == null || javaClass != o.javaClass) {
            return false
        }

        val that = o as TypeCheckException

        return if (mistypedExpression != null) mistypedExpression == that.mistypedExpression else that.mistypedExpression == null
    }

    companion object {
        private const val serialVersionUID = 1L
    }
}
