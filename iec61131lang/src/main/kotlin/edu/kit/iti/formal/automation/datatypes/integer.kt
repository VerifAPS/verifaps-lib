package edu.kit.iti.formal.automation.datatypes

import java.math.BigInteger
import java.util.*

open class AnyInt(var bitLength: kotlin.Int = 0, var isSigned: Boolean = false) : AnyNum() {
    open val upperBound: BigInteger
        get() =
            if (isSigned)
                BigInteger.ONE.shiftLeft(bitLength - 1).subtract(BigInteger.ONE)
            else
                BigInteger.ONE.shiftLeft(bitLength).subtract(BigInteger.ONE)

    open val lowerBound: BigInteger
        get() {
            if (isSigned)
                return BigInteger.ZERO
            else {
                return BigInteger.ONE.shiftLeft(bitLength - 1).negate()
            }
        }

    constructor(bitLength: kotlin.Int) : this(bitLength, true)


    override fun repr(obj: Any): String {
        return javaClass.getSimpleName().toUpperCase() + "#" + obj
    }

    open fun next(): Optional<out AnyInt> = Optional.empty()

    open fun asUnsigned() = if (isSigned) AnyInt(bitLength, false) else this
    open fun asSigned() = if (isSigned) this else AnyInt(bitLength, true)

    open fun isValid(value: Long): Boolean {
        val v = BigInteger.valueOf(value)
        return lowerBound <= v && v <= upperBound
    }

    override fun equals(o: Any?): Boolean {
        if (this === o) return true
        if (o !is AnyInt) return false

        val anyInt = o as AnyInt?

        return if (bitLength != anyInt!!.bitLength) false else isSigned == anyInt.isSigned

    }

    override fun hashCode(): kotlin.Int {
        var result = bitLength
        result = 31 * result + if (isSigned) 1 else 0
        return result
    }

    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }

    companion object {
        fun getDataTypeFor(number: Int, unsigned: Boolean): AnyInt {
            val values: Array<AnyInt>
            if (unsigned)
                values = arrayOf(USINT, UINT, ULINT, UDINT)
            else
                values = arrayOf(SINT, INT, LINT, DINT)

            val bits = Math.ceil(Math.log(number.toDouble()) / Math.log(2.0)).toInt()

            for (candidate in values) {
                if (candidate.bitLength >= bits)
                    return candidate
            }

            if (bits < 0)
                return if (unsigned) USINT else SINT

            /*for (AnyInt bit : values)
            if (bit.getBitLength() >= bits)
                return bit;*/

            return if (unsigned)
                AnyInt(bits, false)
            else
                AnyInt(bits, true)
        }
    }
}

object ANY_INT : AnyInt(-1, true)

object UDINT : AnyInt(32, false) {
    override fun next(): Optional<AnyInt> = Optional.of(ULINT)
    override fun asUnsigned() = this
    override fun asSigned() = LINT
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}


object ULINT : AnyInt(64, false) {
    override fun next() = Optional.empty<AnyInt>()
    override fun asSigned() = LINT
    override fun asUnsigned() = this
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}


object SINT : AnyInt(8) {
    override fun next() = Optional.of(INT)
    override fun asSigned() = this
    override fun asUnsigned() = USINT
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}

object USINT : AnyInt(8, false) {
    override fun asUnsigned() = this
    override fun next() = Optional.of(UINT)
    override fun asSigned() = SINT
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}


object INT : AnyInt(16) {
    override fun next() = Optional.ofNullable(DINT)
    override fun asUnsigned() = UINT
    override fun asSigned() = this
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}


object UINT : AnyInt(16, false) {
    override fun next() = Optional.ofNullable(UDINT)
    override fun asUnsigned() = UINT
    override fun asSigned() = INT
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}


object LINT : AnyInt(64) {
    override fun next() = Optional.empty<AnyInt>()

    override fun asSigned() = this
    override fun asUnsigned() = ULINT
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}


object UInt : AnyInt(16, false) {
    override fun next(): Optional<AnyInt> {
        return Optional.of(UDINT)
    }

    override fun asUnsigned() = this
    override fun asSigned(): AnyInt {
        return DINT
    }

    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}


object DINT : AnyInt(32) {
    override fun next(): Optional<AnyInt> {
        return Optional.ofNullable(LINT)
    }

    override fun asSigned() = this
    override fun asUnsigned() = UDINT

    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
        return visitor.visit(this)
    }
}


/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
data class RangeType(
        var bottom: BigInteger = BigInteger.ZERO,
        var top: BigInteger = BigInteger.ZERO,
        var base: AnyInt = INT) : AnyInt(base.bitLength, base.isSigned) {

    override val upperBound: BigInteger
        get() = top

    override val lowerBound: BigInteger
        get() = bottom

    override fun repr(obj: Any) = base.repr(obj)
    override fun next(): Optional<AnyInt> = Optional.empty()
    override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
}
