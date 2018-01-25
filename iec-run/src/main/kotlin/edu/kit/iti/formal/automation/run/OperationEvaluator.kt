package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.AnyInt
import edu.kit.iti.formal.automation.datatypes.AnyReal
import edu.kit.iti.formal.automation.datatypes.DataTypes
import edu.kit.iti.formal.automation.datatypes.promotion.IntegerPromotion
import edu.kit.iti.formal.automation.datatypes.promotion.RealPromotion
import edu.kit.iti.formal.automation.datatypes.values.Values
import edu.kit.iti.formal.automation.run.stexceptions.TypeMissmatchException
import java.math.BigDecimal
import java.math.BigInteger

/**
 * OperationEvaluator executes an ST operator on given ExpressionValues.
 * If Operation if illegal, an error will be thrown
 */
object OperationEvaluator {
    fun add(leftValue: ExpressionValue, rightValue: ExpressionValue): ExpressionValue {
        return when {
            leftValue is Values.VAnyReal || rightValue is Values.VAnyReal -> add(toReal(leftValue), toReal(rightValue))
            leftValue is Values.VAnyInt && rightValue is Values.VAnyInt -> add(leftValue, rightValue)
            else -> throw TypeMissmatchException("must be numbers")
        }
    }


    /**
     * normalize the Expression's Value to its DataType
     */
    public fun normalizeInt(value: Values.VAnyInt) : Values.VAnyInt {
        val type  = value.dataType
        //if negative and unsigned -> offset value into positive region
        val mask = BigInteger.valueOf(2).pow(type.bitLength).subtract(BigInteger.valueOf(1))
        if(!type.isSigned && value.value < BigInteger.ZERO) {
            TODO("make positive")
        }
        var newValue = value.value
        while (newValue > type.upperBound) {
            newValue -= (type.upperBound - type.lowerBound + BigInteger.valueOf(1))
        }

        return Values.VAnyInt(type, newValue)
    }

    private fun add(leftValue: Values.VAnyInt, rightValue: Values.VAnyInt): Values.VAnyInt {
        val integerPromotion = IntegerPromotion()
        val promotedType = integerPromotion.getPromotion(leftValue.dataType, rightValue.dataType)
         if (promotedType is AnyInt) {
            return normalizeInt(Values.VAnyInt(promotedType,
                    leftValue.value.add(rightValue.value)))
        }
        TODO("choose correct datatype and modulo the addition")
    }

    private fun add(leftValue: Values.VAnyReal, rightValue: Values.VAnyReal): Values.VAnyReal {
        val realPromotion = RealPromotion()
        val promotedType = realPromotion.getPromotion(leftValue.dataType, rightValue.dataType)
        if (promotedType is AnyReal) {
            return Values.VAnyReal(promotedType, leftValue.value)
        }
        throw TypeMissmatchException("could not promote '${leftValue.value}+${rightValue.value}' to appropriate type");
    }


    fun multiply(leftValue: ExpressionValue, rightValue: ExpressionValue): ExpressionValue {
        return when {
            leftValue is Values.VAnyInt && rightValue is Values.VAnyInt -> multiply(leftValue, rightValue)
            else -> TODO("implement other data type")
        }
    }

    fun multiply(leftValue: Values.VAnyInt, rightValue: Values.VAnyInt) : Values.VAnyInt {
        return normalizeInt(Values.VAnyInt(leftValue.dataType, leftValue.value.multiply(rightValue.value)))
    }


    fun not(expressionValue: ExpressionValue): ExpressionValue {
        if (expressionValue is Values.VBool) {
            return Values.VBool(expressionValue.dataType, expressionValue.value.not())
        } else {
            throw TypeMissmatchException("must be bool")
        }
    }

    fun negate(expressionValue: ExpressionValue): ExpressionValue {
        return when (expressionValue) {
            is Values.VAnyInt -> normalizeInt(
                    Values.VAnyInt(expressionValue.dataType.asSigned(), expressionValue.value.negate()))
            is Values.VAnyReal -> Values.VAnyReal(expressionValue.dataType, expressionValue.value.negate())
            else -> throw TypeMissmatchException("must be a number")
        }
    }

    fun equalValues(leftValue: ExpressionValue, rightValue: ExpressionValue): ExpressionValue {
        //TODO promote types for equals comparison and make compare data types
        return Values.VBool(AnyBit.BOOL, leftValue.value == rightValue.value)
    }

    fun notEquals(leftValue: ExpressionValue, rightValue: ExpressionValue): ExpressionValue {
        return not(equalValues(leftValue, rightValue))
    }

    fun and(leftValue: ExpressionValue, rightValue: ExpressionValue): Values.VBool {
        if (leftValue is Values.VBool && rightValue is Values.VBool) {
            return Values.VBool(AnyBit.BOOL, leftValue.value && rightValue.value)
        } else {
            throw TypeMissmatchException("operator \"and\" can only be applied to boolean values")
        }
    }

    private fun greaterThan(leftValue: Values.VAnyInt, rightValue: Values.VAnyInt)=
            Values.VBool(AnyBit.BOOL, leftValue.value > rightValue.value)

    private fun greaterThan(leftValue: Values.VAnyReal, rightValue: Values.VAnyReal)=
            Values.VBool(AnyBit.BOOL, leftValue.value > rightValue.value)

    fun greaterThan(leftValue: ExpressionValue, rightValue: ExpressionValue): Values.VBool {
        return when {
            leftValue is Values.VAnyReal || rightValue is Values.VAnyReal -> greaterThan(toReal(leftValue), toReal(rightValue))
            leftValue is Values.VAnyInt && rightValue is Values.VAnyInt -> greaterThan(leftValue, rightValue)
            else -> throw TypeMissmatchException("must be a number")
        }
    }

    private fun greaterThanOrEquals(leftValue: Values.VAnyInt, rightValue: Values.VAnyInt)=
            Values.VBool(AnyBit.BOOL, leftValue.value >= rightValue.value)

    private fun greaterThanOrEquals(leftValue: Values.VAnyReal, rightValue: Values.VAnyReal)=
            Values.VBool(AnyBit.BOOL, leftValue.value >= rightValue.value)

    fun greaterThanOrEquals(leftValue: ExpressionValue, rightValue: ExpressionValue): Values.VBool {
        return when {
            leftValue is Values.VAnyReal || rightValue is Values.VAnyReal -> greaterThanOrEquals(toReal(leftValue), toReal(rightValue))
            leftValue is Values.VAnyInt && rightValue is Values.VAnyInt -> greaterThanOrEquals(leftValue, rightValue)
            else -> throw TypeMissmatchException("must be a number")
        }
    }

    private fun lessThanOrEquals(leftValue: Values.VAnyInt, rightValue: Values.VAnyInt)=
            Values.VBool(AnyBit.BOOL, leftValue.value <= rightValue.value)

    private fun lessThanOrEquals(leftValue: Values.VAnyReal, rightValue: Values.VAnyReal)=
            Values.VBool(AnyBit.BOOL, leftValue.value <= rightValue.value)

    fun lessThanOrEquals(leftValue: ExpressionValue, rightValue: ExpressionValue): Values.VBool {
        return when {
            leftValue is Values.VAnyReal || rightValue is Values.VAnyReal -> lessThanOrEquals(toReal(leftValue), toReal(rightValue))
            leftValue is Values.VAnyInt && rightValue is Values.VAnyInt -> lessThanOrEquals(leftValue, rightValue)
            else -> throw TypeMissmatchException("must be a number")
        }
    }

    private fun lessThan(leftValue: Values.VAnyInt, rightValue: Values.VAnyInt)=
            Values.VBool(AnyBit.BOOL, leftValue.value < rightValue.value)

    private fun lessThan(leftValue: Values.VAnyReal, rightValue: Values.VAnyReal)=
            Values.VBool(AnyBit.BOOL, leftValue.value < rightValue.value)


    fun lessThan(leftValue: ExpressionValue, rightValue: ExpressionValue): Values.VBool {
        return when {
            leftValue is Values.VAnyReal || rightValue is Values.VAnyReal -> lessThan(toReal(leftValue), toReal(rightValue))
            leftValue is Values.VAnyInt && rightValue is Values.VAnyInt -> lessThan(leftValue, rightValue)
            else -> throw TypeMissmatchException("must be a number")
        }
    }

    private fun toReal(expressionValue: ExpressionValue): Values.VAnyReal {
        val content = expressionValue.value
        return Values.VAnyReal(AnyReal.REAL, when(content) {
            is BigInteger -> BigDecimal(content)
            is BigDecimal -> content
            else -> throw TypeMissmatchException("cannot be a real number")
        })
    }

    fun subtract(leftValue: ExpressionValue, rightValue: ExpressionValue): ExpressionValue {
        return add(leftValue, negate(rightValue))
    }

    fun modulo(leftValue: Values.VAnyInt, rightValue: Values.VAnyInt) =
            Values.VAnyInt(leftValue.dataType, leftValue.value.mod(rightValue.value))

    fun modulo(leftValue: ExpressionValue, rightValue: ExpressionValue): ExpressionValue {
        return when {
            leftValue is Values.VAnyInt && rightValue is Values.VAnyInt -> modulo(leftValue, rightValue)
            else -> throw TypeMissmatchException("modulo expects both to be int")
        }
    }

    fun or(leftValue: Values.VBool, rightValue: Values.VBool) =
            Values.VBool(leftValue.dataType, leftValue.value || rightValue.value)

    fun or(leftValue: ExpressionValue, rightValue: ExpressionValue): ExpressionValue {
        return when {
            leftValue is Values.VBool && rightValue is Values.VBool -> or(leftValue, rightValue)
            else -> throw TypeMissmatchException("or expects booleans")
        }
    }
}