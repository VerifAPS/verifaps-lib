package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.AnyInt
import edu.kit.iti.formal.automation.datatypes.AnyReal
import edu.kit.iti.formal.automation.datatypes.promoteWith
import edu.kit.iti.formal.automation.datatypes.values.VAnyInt
import edu.kit.iti.formal.automation.datatypes.values.VAnyReal
import edu.kit.iti.formal.automation.datatypes.values.VBool
import edu.kit.iti.formal.automation.run.stexceptions.TypeMissmatchException
import java.math.BigDecimal
import java.math.BigInteger

/**
 * OperationEvaluator executes an ST operator on given Expression
 * If Operation if illegal, an error will be thrown
 */
object OperationEvaluator {
    fun add(leftValue: EValue, rightValue: EValue): EValue {
        return when {
            leftValue is VAnyReal || rightValue is VAnyReal -> add(toReal(leftValue), toReal(rightValue))
            leftValue is VAnyInt && rightValue is VAnyInt -> add(leftValue, rightValue)
            else -> throw TypeMissmatchException("must be numbers")
        }
    }


    /**
     * normalize the Expression's Value to its DataType
     */
    public fun normalizeInt(value: VAnyInt): VAnyInt {
        val (type, v) = value
        if (type.isValid(v)) return value
        //if negative and unsigned -> offset value into positive region
        val mask = BigInteger.valueOf(2).pow(type.bitLength).subtract(BigInteger.valueOf(1))
        if (!type.isSigned && value.value < BigInteger.ZERO) {
            return VAnyInt(type, -v) //TODO not correct overflow
        }
        var newValue = value.value
        while (newValue > type.upperBound) {
            newValue -= (type.upperBound - type.lowerBound + BigInteger.valueOf(1))
        }
        return VAnyInt(type, newValue)
    }

    private fun add(leftValue: VAnyInt, rightValue: VAnyInt): VAnyInt {
        val promotedType = leftValue.dataType promoteWith rightValue.dataType
        if (promotedType is AnyInt) {
            return normalizeInt(VAnyInt(promotedType,
                    leftValue.value.add(rightValue.value)))
        }
        TODO("choose correct datatype and modulo the addition")
    }

    private fun add(leftValue: VAnyReal, rightValue: VAnyReal): VAnyReal {
        val promotedType = (leftValue.dataType promoteWith rightValue.dataType)
        if (promotedType is AnyReal) {
            return VAnyReal(promotedType, leftValue.value)
        }
        throw TypeMissmatchException("could not promote '${leftValue.value}+${rightValue.value}' to appropriate type");
    }


    fun multiply(leftValue: EValue, rightValue: EValue): EValue {
        return when {
            leftValue is VAnyInt && rightValue is VAnyInt -> multiply(leftValue, rightValue)
            else -> TODO("implement other data type")
        }
    }

    fun multiply(leftValue: VAnyInt, rightValue: VAnyInt): VAnyInt {
        return normalizeInt(VAnyInt(leftValue.dataType, leftValue.value.multiply(rightValue.value)))
    }


    fun not(eValue: EValue): EValue {
        if (eValue is VBool) {
            return VBool(eValue.dataType, eValue.value.not())
        } else {
            throw TypeMissmatchException("must be bool")
        }
    }

    fun negate(eValue: EValue): EValue = when (eValue) {
        is VAnyInt ->
            normalizeInt(
                    VAnyInt(
                            eValue.dataType.asSigned(),
                            eValue.value.negate()
                    ))
        is VAnyReal -> VAnyReal(eValue.dataType, eValue.value.negate())
        else -> throw TypeMissmatchException("must be a number")
    }

    fun equalValues(leftValue: EValue, rightValue: EValue): EValue {
        //TODO promote types for equals comparison and make compare data types
        return VBool(AnyBit.BOOL, leftValue.value == rightValue.value)
    }

    fun notEquals(leftValue: EValue, rightValue: EValue): EValue {
        return not(equalValues(leftValue, rightValue))
    }

    fun and(leftValue: EValue, rightValue: EValue): VBool {
        if (leftValue is VBool && rightValue is VBool) {
            return VBool(AnyBit.BOOL, leftValue.value && rightValue.value)
        } else {
            throw TypeMissmatchException("operator \"and\" can only be applied to boolean values")
        }
    }

    private fun greaterThan(leftValue: VAnyInt, rightValue: VAnyInt) =
            VBool(AnyBit.BOOL, leftValue.value > rightValue.value)

    private fun greaterThan(leftValue: VAnyReal, rightValue: VAnyReal) =
            VBool(AnyBit.BOOL, leftValue.value > rightValue.value)

    fun greaterThan(leftValue: EValue, rightValue: EValue): VBool {
        return when {
            leftValue is VAnyReal || rightValue is VAnyReal -> greaterThan(toReal(leftValue), toReal(rightValue))
            leftValue is VAnyInt && rightValue is VAnyInt -> greaterThan(leftValue, rightValue)
            else -> throw TypeMissmatchException("must be a number")
        }
    }

    private fun greaterThanOrEquals(leftValue: VAnyInt, rightValue: VAnyInt) =
            VBool(AnyBit.BOOL, leftValue.value >= rightValue.value)

    private fun greaterThanOrEquals(leftValue: VAnyReal, rightValue: VAnyReal) =
            VBool(AnyBit.BOOL, leftValue.value >= rightValue.value)

    fun greaterThanOrEquals(leftValue: EValue, rightValue: EValue): VBool {
        return when {
            leftValue is VAnyReal || rightValue is VAnyReal -> greaterThanOrEquals(toReal(leftValue), toReal(rightValue))
            leftValue is VAnyInt && rightValue is VAnyInt -> greaterThanOrEquals(leftValue, rightValue)
            else -> throw TypeMissmatchException("must be a number")
        }
    }

    private fun lessThanOrEquals(leftValue: VAnyInt, rightValue: VAnyInt) =
            VBool(AnyBit.BOOL, leftValue.value <= rightValue.value)

    private fun lessThanOrEquals(leftValue: VAnyReal, rightValue: VAnyReal) =
            VBool(AnyBit.BOOL, leftValue.value <= rightValue.value)

    fun lessThanOrEquals(leftValue: EValue, rightValue: EValue): VBool {
        return when {
            leftValue is VAnyReal || rightValue is VAnyReal -> lessThanOrEquals(toReal(leftValue), toReal(rightValue))
            leftValue is VAnyInt && rightValue is VAnyInt -> lessThanOrEquals(leftValue, rightValue)
            else -> throw TypeMissmatchException("must be a number")
        }
    }

    private fun lessThan(leftValue: VAnyInt, rightValue: VAnyInt) =
            VBool(AnyBit.BOOL, leftValue.value < rightValue.value)

    private fun lessThan(leftValue: VAnyReal, rightValue: VAnyReal) =
            VBool(AnyBit.BOOL, leftValue.value < rightValue.value)


    fun lessThan(leftValue: EValue, rightValue: EValue): VBool {
        return when {
            leftValue is VAnyReal || rightValue is VAnyReal -> lessThan(toReal(leftValue), toReal(rightValue))
            leftValue is VAnyInt && rightValue is VAnyInt -> lessThan(leftValue, rightValue)
            else -> throw TypeMissmatchException("must be a number")
        }
    }

    private fun toReal(eValue: EValue): VAnyReal {
        val content = eValue.value
        return VAnyReal(AnyReal.REAL, when (content) {
            is BigInteger -> BigDecimal(content)
            is BigDecimal -> content
            else -> throw TypeMissmatchException("cannot be a real number")
        })
    }

    fun subtract(leftValue: EValue, rightValue: EValue): EValue {
        return add(leftValue, negate(rightValue))
    }

    fun modulo(leftValue: VAnyInt, rightValue: VAnyInt) =
            VAnyInt(leftValue.dataType, leftValue.value.mod(rightValue.value))

    fun modulo(leftValue: EValue, rightValue: EValue): EValue {
        return when {
            leftValue is VAnyInt && rightValue is VAnyInt -> modulo(leftValue, rightValue)
            else -> throw TypeMissmatchException("modulo expects both to be int")
        }
    }

    fun or(leftValue: VBool, rightValue: VBool) =
            VBool(leftValue.dataType, leftValue.value || rightValue.value)

    fun or(leftValue: EValue, rightValue: EValue): EValue {
        return when {
            leftValue is VBool && rightValue is VBool -> or(leftValue, rightValue)
            else -> throw TypeMissmatchException("or expects booleans")
        }
    }
}