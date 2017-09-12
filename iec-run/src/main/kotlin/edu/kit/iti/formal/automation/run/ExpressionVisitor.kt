package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.EnumerateType
import edu.kit.iti.formal.automation.datatypes.values.Values
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.run.stexceptions.ExecutionException
import edu.kit.iti.formal.automation.scope.LocalScope
import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import edu.kit.iti.formal.automation.visitors.Visitable

/**
 * evaluates the expression given via .visit() and runs creates a Runtime to call on functions in the expression.
 * ExpressionVisitor resolves variable values in [state] and declarations in [localScope]
 * ExpressionVisitor may modifies [state] indirectly through Runtime
 */
class ExpressionVisitor(private val state : State, private val localScope : LocalScope) : DefaultVisitor<ExpressionValue>() {

    override fun defaultVisit(visitable: Visitable?): ExpressionValue {
        TODO("missing visitor for visitable ${visitable.toString()}")
    }

    override fun visit(functionCall: FunctionCall): ExpressionValue {

        val innerState = NestedState(state)
        val functionDeclaration = localScope.globalScope.resolveFunction(functionCall, localScope)
        return functionCall.function.accept(ExpressionVisitor(innerState, functionDeclaration.localScope))
    }

    override fun visit(unaryExpression: UnaryExpression): ExpressionValue {
        //"as ExpressionValue" should not be necessary, but the compiler complains otherwise
        // I see no way, where the result of .accept() will not be a ExpressionValue
        val expressionValue = unaryExpression.expression.accept<ExpressionValue>(this) as ExpressionValue
        return when(unaryExpression.operator) {
            Operators.NOT -> OperationEvaluator.not(expressionValue)
            Operators.MINUS -> OperationEvaluator.negate(expressionValue)
            else -> throw IllegalStateException("no other unary Operator")
        }
    }

    override fun visit(literal: Literal) : ExpressionValue {
        try {
            return literal.asValue()
        } catch (npe : NullPointerException) {

            val identifier = literal.dataTypeName
            val resolvedDataType = localScope.globalScope.resolveDataType(identifier)
            if (resolvedDataType is EnumerateType) {
                return Values.VAnyEnum(resolvedDataType, literal.textValue)
            }
        }
        TODO("implement other cases for $literal")
    }

    override fun visit(symbolicReference: SymbolicReference): ExpressionValue {
        val variableName = symbolicReference.identifier

        val variableState = state[variableName]
                ?: throw ExecutionException("Variable $variableName not found")

        return variableState
                .orElseThrow { throw ExecutionException("Variable $variableName not initialized") }
    }

    override fun visit(binaryExpression: BinaryExpression): ExpressionValue {
        val leftValue = binaryExpression.leftExpr.accept<ExpressionValue>(this) as ExpressionValue
        val rightValue = binaryExpression.rightExpr.accept<ExpressionValue>(this) as ExpressionValue
        return when(binaryExpression.operator) {
            Operators.ADD -> OperationEvaluator.add(leftValue, rightValue)
            Operators.EQUALS -> OperationEvaluator.equalValues(leftValue, rightValue)
            Operators.AND -> OperationEvaluator.and(leftValue, rightValue)
            Operators.GREATER_THAN -> OperationEvaluator.greaterThan(leftValue, rightValue)
            else -> TODO("operator ${binaryExpression.operator.symbol()} is not implemented")
        }
    }


}

