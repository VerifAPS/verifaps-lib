package edu.kit.iti.formal.stvs.model.expressions

import edu.kit.iti.formal.stvs.model.expressions.ValueBool.Companion.of

/**
 * Created by philipp on 17.01.17.
 */
object SimpleExpressions {
    fun negate(e: Expression?): Expression {
        return UnaryFunctionExpr(UnaryFunctionExpr.Op.UNARY_MINUS, e)
    }

    fun not(e: Expression?): Expression {
        return UnaryFunctionExpr(UnaryFunctionExpr.Op.NOT, e)
    }

    fun and(e1: Expression?, e2: Expression?): Expression {
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.AND, e1!!, e2!!)
    }

    fun plus(e1: Expression?, e2: Expression?): Expression {
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.PLUS, e1!!, e2!!)
    }

    fun minus(e1: Expression?, e2: Expression?): Expression {
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.PLUS, e1!!, e2!!)
    }

    fun equal(e1: Expression?, e2: Expression?): Expression {
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.EQUALS, e1!!, e2!!)
    }

    fun lessThan(e1: Expression?, e2: Expression?): Expression {
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.LESS_THAN, e1!!, e2!!)
    }

    fun lessEqual(e1: Expression?, e2: Expression?): Expression {
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.LESS_EQUALS, e1!!, e2!!)
    }

    fun greaterEqual(e1: Expression?, e2: Expression?): Expression {
        return BinaryFunctionExpr(BinaryFunctionExpr.Op.GREATER_EQUALS, e1!!, e2!!)
    }


    fun variable(name: String?): Expression {
        return VariableExpr(name)
    }

    fun variable(name: String?, index: Int): Expression {
        return VariableExpr(name, index)
    }

    fun literal(integer: Int): Expression {
        return LiteralExpr(ValueInt(integer))
    }

    fun literal(bool: Boolean): Expression {
        return LiteralExpr(of(bool))
    }

    fun literal(e: ValueEnum?): Expression {
        return LiteralExpr(e!!)
    }

    fun literalEnum(value: String?, sourceType: TypeEnum?): Expression {
        return literal(ValueEnum(value!!, sourceType!!))
    }
}
