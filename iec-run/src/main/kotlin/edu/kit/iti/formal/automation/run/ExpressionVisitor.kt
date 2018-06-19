package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.run.stexceptions.ExecutionException
import edu.kit.iti.formal.automation.scope.Scope
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitorNN

class ExpressionVisitor(private val state: State,
                        private val scope: Scope) : DefaultVisitorNN<EValue>() {

    override fun defaultVisit(obj: Any) =
            TODO("missing visitor for visitable ${obj.toString()}")

    override fun visit(parameter: InvocationParameter): EValue = parameter.expression.accept(this)


    override fun visit(functionCall: Invocation): EValue {
        val functionDeclaration = scope.resolveFunction(functionCall.calleeName)
        if (functionDeclaration == null)
            TODO("Could not find function ${functionCall.calleeName}")
        val evaluatedParams = functionCall.parameters.map { it.accept(this)!! }
        val returnValue = ExecutionFacade.evaluateFunction(functionDeclaration, evaluatedParams)
        return returnValue
        /*
        if (returnValue != null) {
            throw ExecutionException("Return value not set in function '${functionCall.calleeName}' declaration")
        }
        throw ExecutionException("Return value not initialized in function ${functionCall.calleeName}")*/
    }

    override fun visit(unaryExpression: UnaryExpression): EValue {
        //"as EValue" should not be necessary, but the compiler complains otherwise
        // I see no way, where the result of .accept() will not be a EValue
        val expressionValue = unaryExpression.expression.accept(this)
        return when (unaryExpression.operator) {
            Operators.NOT -> OperationEvaluator.not(expressionValue)
            Operators.MINUS -> OperationEvaluator.negate(expressionValue)
            else -> throw IllegalStateException("no other unary Operator")
        }
    }

    override fun visit(literal: Literal): EValue {
        /*literal.asValue() does either throw an exception or returns null, if no direct value isType available
        DISCUSS: isType this intentional or accidental? better way distinguishing between RefTo and other?
        (isType RefTo) did not work  -> solve be using resolveDataType*/
        try {
            val asValue = literal.asValue()
            if (asValue != null) {
                return asValue
            }
        } catch (npe: NullPointerException) {

        }

        /*val resolvedDataType = literal.dataType()
        if (resolvedDataType is EnumerateType) {
            return VAnyEnum(resolvedDataType, literal.textValue!!)
        }
        //DISCUSS: Time-Literal has resolvedDataType LREAL ?!
        if (resolvedDataType is TimeType) {
            TODO()
            //return Values.VAnyReal(resolvedDataType, BigDecimal.valueOf(0))
        }
    */
        TODO("implement other cases for $literal")
    }


    override fun visit(symbolicReference: SymbolicReference): EValue {
        val variableName = symbolicReference.asPath()
        val variableState = state[variableName]
                ?: throw ExecutionException("Variable $variableName not found")
        return variableState
        /*
        var dataType = symbolicReference.dataType(scope)
        if (dataType is FunctionBlockDataType) {
            val structValue = state[symbolicReference.identifier]!!//.orElseThrow { ExecutionException("variable not defined") }.value
            if (symbolicReference.sub != null && structValue is Map<*, *>) {
                val matching = structValue.filter {
                    it.key == (symbolicReference.sub as SymbolicReference).identifier
                }.values.first()
                if (matching != null && matching is EValue) {
                    return matching
                }
            }
            TODO();
        }

        return variableState
        //.orElseThrow { throw ExecutionException("Variable $variableName not initialized") }
*/
    }

    override fun visit(binaryExpression: BinaryExpression): EValue {
        val leftValue = binaryExpression.leftExpr.accept<EValue>(this) as EValue
        val rightValue = binaryExpression.rightExpr.accept<EValue>(this) as EValue

        //TODO resolve function by using dataType
        //binaryExpression.dataType(scope)

        return when (binaryExpression.operator) {
            Operators.ADD -> OperationEvaluator.add(leftValue, rightValue)
            Operators.MULT -> OperationEvaluator.multiply(leftValue, rightValue)
            Operators.EQUALS -> OperationEvaluator.equalValues(leftValue, rightValue)
            Operators.NOT_EQUALS -> OperationEvaluator.notEquals(leftValue, rightValue)
            Operators.GREATER_THAN -> OperationEvaluator.greaterThan(leftValue, rightValue)
            Operators.GREATER_EQUALS -> OperationEvaluator.greaterThanOrEquals(leftValue, rightValue)
            Operators.LESS_THAN -> OperationEvaluator.lessThan(leftValue, rightValue)
            Operators.LESS_EQUALS -> OperationEvaluator.lessThanOrEquals(leftValue, rightValue)
            Operators.AND -> OperationEvaluator.and(leftValue, rightValue)
            Operators.OR -> OperationEvaluator.or(leftValue, rightValue)
            Operators.SUB -> OperationEvaluator.subtract(leftValue, rightValue)
            Operators.MOD -> OperationEvaluator.modulo(leftValue, rightValue)
            else -> TODO("operator ${binaryExpression.operator.symbol} isType not implemented (${binaryExpression.operator.toString()})")
        }
    }


}

