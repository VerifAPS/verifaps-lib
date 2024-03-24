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
            return expr!!.takeVisitor(this)
        } catch (runtimeException: InternalTypeCheckException) {
            throw TypeCheckException(
                runtimeException.mistypedExpression,
                runtimeException.message
            )
        }
    }

    override fun visitUnaryFunction(unaryFunctionExpr: UnaryFunctionExpr): Type {
        val argType = unaryFunctionExpr.argument!!.takeVisitor(this)
        when (unaryFunctionExpr.operation) {
            UnaryFunctionExpr.Op.NOT -> {
                assertTypeEquality(TypeBool.BOOL, argType, unaryFunctionExpr)
                return TypeBool.BOOL
            }

            UnaryFunctionExpr.Op.UNARY_MINUS -> {
                assertTypeEquality(TypeInt.INT, argType, unaryFunctionExpr)
                return TypeInt.INT
            }

            else -> return throwUnkownOperation(unaryFunctionExpr.operation.toString(), unaryFunctionExpr)
        }
    }

    override fun visitBinaryFunction(binaryFunctionExpr: BinaryFunctionExpr): Type {
        val firstArgType = binaryFunctionExpr.firstArgument.takeVisitor(this)
        val secondArgType = binaryFunctionExpr.secondArgument.takeVisitor(this)
        when (binaryFunctionExpr.operation) {
            BinaryFunctionExpr.Op.PLUS, BinaryFunctionExpr.Op.MINUS, BinaryFunctionExpr.Op.MULTIPLICATION, BinaryFunctionExpr.Op.DIVISION, BinaryFunctionExpr.Op.MODULO, BinaryFunctionExpr.Op.POWER -> {
                assertTypeEquality(TypeInt.INT, firstArgType, binaryFunctionExpr)
                assertTypeEquality(TypeInt.INT, secondArgType, binaryFunctionExpr)
                return TypeInt.INT
            }

            BinaryFunctionExpr.Op.AND, BinaryFunctionExpr.Op.OR, BinaryFunctionExpr.Op.XOR -> {
                assertTypeEquality(TypeBool.BOOL, firstArgType, binaryFunctionExpr)
                assertTypeEquality(TypeBool.BOOL, secondArgType, binaryFunctionExpr)
                return TypeBool.BOOL
            }

            BinaryFunctionExpr.Op.GREATER_THAN, BinaryFunctionExpr.Op.GREATER_EQUALS, BinaryFunctionExpr.Op.LESS_THAN, BinaryFunctionExpr.Op.LESS_EQUALS -> {
                assertTypeEquality(TypeInt.INT, firstArgType, binaryFunctionExpr)
                assertTypeEquality(TypeInt.INT, secondArgType, binaryFunctionExpr)
                return TypeBool.BOOL
            }

            BinaryFunctionExpr.Op.EQUALS, BinaryFunctionExpr.Op.NOT_EQUALS -> {
                assertEqualTypes(firstArgType, secondArgType, binaryFunctionExpr)
                return TypeBool.BOOL
            }

            else -> return throwUnkownOperation(
                binaryFunctionExpr.operation.toString(),
                binaryFunctionExpr
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

    override fun visitLiteral(literalExpr: LiteralExpr): Type {
        return literalExpr.value.type
    }

    override fun visitVariable(variableExpr: VariableExpr): Type {
        val varType = variableTypeContext[variableExpr.variableName]
        if (varType == null) {
            throw InternalTypeCheckException(
                variableExpr,
                "Don't know type of variable: " + variableExpr.variableName
            )
        } else {
            return varType
        }
    }
}
