package edu.kit.iti.formal.stvs.model.expressions

/**
 * The runtime-representation for parsed, binary function expressions. Examples are: +, -, =, AND,
 * OR, etc. Anything that has two arguments.
 * @param operation the [Op] that this expression should do with its arguments.
 * @param firstArgument the first (or left) argument
 * @param secondArgument the second (or right) argument
 * @author Philipp
 */
data class BinaryFunctionExpr(
    val operation: Op,
    val firstArgument: Expression,
    val secondArgument: Expression
) : Expression() {
    enum class Op {
        // (BOOL, BOOL) -> BOOL
        AND, OR, XOR,

        // (INT, INT) -> BOOL
        GREATER_THAN, GREATER_EQUALS, LESS_THAN, LESS_EQUALS,

        // (a, a) -> BOOL
        EQUALS, NOT_EQUALS,

        // (INT, INT) -> INT
        PLUS, MINUS, MULTIPLICATION, DIVISION, MODULO, POWER
    }

    override fun <R> accept(visitor: ExpressionVisitor<R>): R {
        return visitor.visitBinaryFunction(this)
    }


    override fun toString(): String {
        return "Bin($firstArgument $operation $secondArgument)"
    }
}