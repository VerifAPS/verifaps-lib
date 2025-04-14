package edu.kit.iti.formal.stvs.model.expressions

/**
 * A type checker for [Expression]s.
 * If an ill-typed expression is encountered, this class produces a [TypeCheckException].
 *
 * @author Philipp
 */
class TypeChecker
/**
 * Since the [Expression] AST does not know about the type of a variable (see
 * [VariableExpr]), this class needs a type context for variables.
 * The type checker does not handle free- or IoVariables differently. Both are reduced to their
 * string representation.
 *
 * @param variableTypeContext a map from variable names to types.
 */(private val variableTypeContext: Map<String, Type>) : ExpressionVisitor<Type> {
    private class InternalTypeCheckException(val mistypedExpression: Expression, message: String?) :
        RuntimeException(message)

    /**
     * Checks the type of an [Expression] or throws a [TypeCheckException] on an ill-typed
     * expression.
     *
     * @param expr the expression to be checked
     * @return the type of the expression, iff not ill-typed.
     * @throws TypeCheckException an exception with information about the type error, if an ill-typed
     * expression is encountered
     */
    @Throws(TypeCheckException::class)
    fun typeCheck(expr: Expression?): Type? {
        try {
            return expr!!.accept(this)
        } catch (runtimeException: InternalTypeCheckException) {
            throw TypeCheckException(
                runtimeException.mistypedExpression,
                runtimeException.message
            )
        }
    }

    override fun visitUnaryFunction(unary: UnaryFunctionExpr): Type {
        val argType = unary.argument!!.accept(this)
        when (unary.operation) {
            UnaryFunctionExpr.Op.NOT -> {
                assertTypeEquality(TypeBool, argType, unary)
                return TypeBool
            }

            UnaryFunctionExpr.Op.UNARY_MINUS -> {
                assertTypeEquality(TypeInt, argType, unary)
                return TypeInt
            }

            else -> return throwUnkownOperation(unary.operation.toString(), unary)
        }
    }

    override fun visitBinaryFunction(binary: BinaryFunctionExpr): Type {
        val firstArgType = binary.firstArgument.accept(this)
        val secondArgType = binary.secondArgument.accept(this)
        when (binary.operation) {
            BinaryFunctionExpr.Op.PLUS, BinaryFunctionExpr.Op.MINUS, BinaryFunctionExpr.Op.MULTIPLICATION, BinaryFunctionExpr.Op.DIVISION, BinaryFunctionExpr.Op.MODULO, BinaryFunctionExpr.Op.POWER -> {
                assertTypeEquality(TypeInt, firstArgType, binary)
                assertTypeEquality(TypeInt, secondArgType, binary)
                return TypeInt
            }

            BinaryFunctionExpr.Op.AND, BinaryFunctionExpr.Op.OR, BinaryFunctionExpr.Op.XOR -> {
                assertTypeEquality(TypeBool, firstArgType, binary)
                assertTypeEquality(TypeBool, secondArgType, binary)
                return TypeBool
            }

            BinaryFunctionExpr.Op.GREATER_THAN, BinaryFunctionExpr.Op.GREATER_EQUALS, BinaryFunctionExpr.Op.LESS_THAN, BinaryFunctionExpr.Op.LESS_EQUALS -> {
                assertTypeEquality(TypeInt, firstArgType, binary)
                assertTypeEquality(TypeInt, secondArgType, binary)
                return TypeBool
            }

            BinaryFunctionExpr.Op.EQUALS, BinaryFunctionExpr.Op.NOT_EQUALS -> {
                assertEqualTypes(firstArgType, secondArgType, binary)
                return TypeBool
            }

            else -> return throwUnkownOperation(
                binary.operation.toString(),
                binary
            )
        }
    }

    private fun assertTypeEquality(expectedType: Type, actualType: Type?, expr: Expression) {
        if (!actualType!!.checksAgainst(expectedType)) {
            throw InternalTypeCheckException(
                expr, "Expected type \"" + expectedType.typeName
                        + "\"," + "but got \"" + actualType.typeName + "\""
            )
        }
    }

    // Almost Only differs in error message from assertTypeEquality
    private fun assertEqualTypes(type1: Type?, type2: Type?, expr: Expression) {
        if (type1 != type2) {
            throw InternalTypeCheckException(
                expr,
                "Expected equal types, but got 2 different types: \"" + type1!!.typeName + "\""
                        + " and \"" + type2!!.typeName + "\""
            )
        }
    }

    private fun <A> throwUnkownOperation(operationName: String, expr: Expression): A {
        throw InternalTypeCheckException(expr, "Unknown Operation \"$operationName\"")
    }

    override fun visitLiteral(literal: LiteralExpr): Type {
        return literal.value.type
    }

    override fun visitVariable(expr: VariableExpr): Type {
        val varType = variableTypeContext[expr.variableName]
        if (varType == null) {
            throw InternalTypeCheckException(
                expr,
                "Don't know type of variable: " + expr.variableName
            )
        } else {
            return varType
        }
    }

    override fun visit(expr: GuardedExpression): Type {
        val types = expr.branches.map { (_, b) -> b.accept(this) }
        if (types.any { it != types.first() }) {
            throw TypeCheckException(expr, "Types of cases must be equal")
        }
        return types.first()
    }
}
