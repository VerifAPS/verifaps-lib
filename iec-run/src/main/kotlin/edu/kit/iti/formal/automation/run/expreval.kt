package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.*
import edu.kit.iti.formal.automation.datatypes.values.Value
import edu.kit.iti.formal.automation.datatypes.values.Values
import edu.kit.iti.formal.automation.operators.BinaryOperator
import edu.kit.iti.formal.automation.operators.Operators
import edu.kit.iti.formal.automation.operators.UnaryOperator
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.visitors.DefaultVisitor
import java.math.BigDecimal
import java.math.BigInteger
import edu.kit.iti.formal.automation.datatypes.Any as DataType

/**
 *
 * @author Alexander Weigl
 * @version 1 (23.06.17)
 */

class UnaryExpressionHandler(val operator: UnaryOperator,
                             val type: edu.kit.iti.formal.automation.datatypes.Any,
                             val handler: (Value<*,*>) -> Value<*,*>)

class BinaryExpressionHandler(val operator: BinaryOperator,
                              val typeLeft: edu.kit.iti.formal.automation.datatypes.Any,
                              val typeRight: edu.kit.iti.formal.automation.datatypes.Any,
                              val handler: (Value<*,*>, Value<*,*>) -> Value<*,*>)

object EvalFunctions {
    val unaryMinusEval = UnaryExpressionHandler(Operators.MINUS, AnyNum.ANY_NUM, this::unaryMinusFn)
    private fun unaryMinusFn(it: Value<*,*>): Value<*,*> {
        if (it.dataType is AnyInt && it.value is BigInteger) {
            return Values.VAnyInt((it.dataType as AnyInt?), (it.value as BigInteger).negate())
        }
        if (it.dataType is AnyInt && it.value is BigDecimal) {
            return Values.VAnyReal((it.dataType as AnyReal?), (it.value as BigDecimal).negate())
        }
        throw IllegalStateException()
    }

    val unaryNotEval = UnaryExpressionHandler(Operators.NOT, AnyBit.BOOL, this::unaryNotFn)
    private fun unaryNotFn(it: Value): Value {
        if (it.dataType is AnyBit.Bool && it.obj is Boolean) {
            return Value(it.dataType, !it.obj)
        }
        if (it.dataType is AnyBit && it.obj is Long) {
            return Value(it.dataType, it.obj.inv())
        }
        throw IllegalStateException()
    }


    val binaryPlusEval = BinaryExpressionHandler(Operators.ADD, DataTypes.INT, DataTypes.INT, this::binaryPlusFn)
    private fun binaryPlusFn(a: Value, b: Value): Value {
        if (a.obj is BigInteger && b.obj is BigInteger) {
            return Value(a.dataType, a.obj.add(b.obj))
        }
        throw IllegalStateException()
    }

    val binarySubEval = BinaryExpressionHandler(Operators.SUB, DataTypes.INT, DataTypes.INT, this::binarySubFn)
    private fun binarySubFn(a: Value, b: Value): Value {
        if (a.obj is BigInteger && b.obj is BigInteger) {
            return Value(a.dataType, a.obj.subtract(b.obj))
        }
        throw IllegalStateException()
    }

    val binaryMultEval = BinaryExpressionHandler(Operators.MULT, DataTypes.INT, DataTypes.INT, this::binaryMultFn)
    private fun binaryMultFn(a: Value, b: Value): Value {
        if (a.obj is BigInteger && b.obj is BigInteger) {
            return Value(a.dataType, a.obj.multiply(b.obj))
        }
        throw IllegalStateException()
    }

    val binaryDivEval = BinaryExpressionHandler(Operators.DIV, DataTypes.INT, DataTypes.INT, this::binaryDivFn)
    private fun binaryDivFn(a: Value, b: Value): Value {
        if (a.obj is BigInteger && b.obj is BigInteger) {
            return Value(a.dataType, a.obj.div(b.obj))
        }
        throw IllegalStateException()
    }
}

class ExpressionEval(val state: State) : DefaultVisitor<Value<*, *>>() {
    var ueFunctions: List<UnaryExpressionHandler> = arrayListOf()
    var beFunctions: List<BinaryExpressionHandler> = arrayListOf()

    companion object {
        @JvmStatic fun create(state: State): ExpressionEval {
            val ee = ExpressionEval(state)
            ee.ueFunctions = arrayListOf(EvalFunctions.unaryMinusEval, EvalFunctions.unaryNotEval)
            ee.beFunctions = arrayListOf(EvalFunctions.binaryDivEval, EvalFunctions.binaryMultEval,
                    EvalFunctions.binaryPlusEval, EvalFunctions.binarySubEval)
            return ee
        }
    }

    fun eval(expr: Expression): Value<*,*> {
        return expr.accept(this)
    }


    fun eval(expr: Initialization): Value<*,*> {
        return expr.accept(this)
    }

    override fun visit(sr: SymbolicReference): Value<*,*> {
        return state.get(sr.identifier)!!
    }

    override fun visit(ue: UnaryExpression): Value<*,*> {
        val sub = ue.expression.accept(this)
        for (fn in ueFunctions) {
            if (fn.operator == ue.operator
                    && sub.dataType == fn.type)
                return fn.handler(sub)
        }
        throw IllegalStateException("no function registered")
    }

    override fun visit(be: BinaryExpression): Value<*, *> {
        val left: Value<*, *> = be.leftExpr.accept(this)
        val right: Value<*, *> = be.rightExpr.accept(this) as Value<*, *>

        for (fn in beFunctions) {
            if (fn.operator == be.operator
                    && left.dataType == fn.typeLeft
                    && right.dataType == fn.typeRight)
                return fn.handler(left, right)
        }
        throw IllegalStateException("no function registered")
    }

    override fun visit(fc: FunctionCall): Value<*,*> {
        val funState = StateInitializer.getState(fc.function)
        val inputVars = fc.function.localScope
                .filter { it.isInput || it.isInOut }
                .map { it.name }

        val inputs = fc.parameters.zip(inputVars)
                .forEach {
                    funState.put(it.second, it.first.accept(this))
                }
        StatementEval(funState).eval(fc.function.statements)
        return funState.get(fc.functionName)!!
    }

    override fun visit(sv: Literal): Value<*, *> {
        return sv.asValue()
    }
}
