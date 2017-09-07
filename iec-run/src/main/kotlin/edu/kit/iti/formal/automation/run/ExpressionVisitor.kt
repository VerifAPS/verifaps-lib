package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.datatypes.values.Values
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.scope.LocalScope
import edu.kit.iti.formal.automation.st.ast.BinaryExpression
import edu.kit.iti.formal.automation.st.ast.FunctionCall
import edu.kit.iti.formal.automation.st.ast.Literal
import edu.kit.iti.formal.automation.st.ast.UnaryExpression
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import java.math.BigDecimal

class ExpressionVisitor(private val state : State) : DefaultVisitor<ExpressionValue>() {

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
        return literal.asValue()
    }

    override fun visit(binaryExpression: BinaryExpression): ExpressionValue {
        val leftValue = binaryExpression.leftExpr.accept<ExpressionValue>(this) as ExpressionValue
        val rightValue = binaryExpression.rightExpr.accept<ExpressionValue>(this) as ExpressionValue
        return when(binaryExpression.operator) {
            Operators.ADD -> OperationEvaluator.add(leftValue, rightValue)
            else -> TODO()
        }
    }


}

