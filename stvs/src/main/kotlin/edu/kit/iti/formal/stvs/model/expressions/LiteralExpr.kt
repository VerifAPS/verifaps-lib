package edu.kit.iti.formal.stvs.model.expressions

/**
 * The class for expressions that are constant. Examples are <tt>42</tt>, <tt>TRUE</tt> or
 * <tt>my_enum_constructor</tt>.
 * @author Philipp
 */
data class LiteralExpr(val value: Value) : Expression() {
    override fun <R> takeVisitor(visitor: ExpressionVisitor<R>): R {
        return visitor.visitLiteral(this)
    }

    override fun toString() = "LiteralExpr($value)"
}
