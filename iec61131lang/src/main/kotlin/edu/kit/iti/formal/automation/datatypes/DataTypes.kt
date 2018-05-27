package edu.kit.iti.formal.automation.datatypes

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import java.math.BigInteger
import java.util.*
import java.util.stream.Collectors

/**
 *
 * DataTypes class.
 *
 * @author Alexander Weigl (25.06.2014)
 * @version 1
 */
object DataTypes {
    val DEFAULT = BigInteger.ZERO
    val SINT = SInt()
    val USINT = USInt()
    val UINT = UInt()
    val INT = Int()
    val UDINT = UDInt()
    val DINT = DInt()
    val ULINT = ULInt()
    val LINT = LInt()
    val UNKNWON_SIGNED_INT: AnyInt = AnySignedInt.Arbitrary(-1)
    val UNKNWON_UNSIGNED_INT: AnyUnsignedInt = AnyUnsignedInt.Arbitrary(-1)
    val ANY_INT: AnyInt = object : AnySignedInt(-1) {
        override fun next(): Optional<AnyInt>? {
            return null
        }

        override fun asUnsgined(): AnyUnsignedInt {
            return UNKNWON_UNSIGNED_INT
        }

        override fun asSigned(): AnyInt {
            return UNKNWON_SIGNED_INT
        }

        override fun isValid(value: Long): Boolean {
            return true
        }
    }
    val VOID: AnyDt = object : AnyDt("VOID") {
        override fun repr(obj: Any): String {
            return "void"
        }

        override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
            return null
        }
    }
    internal var map = HashMap<String, AnyDt>()

    /**
     *
     * getDataTypeNames.
     *
     * @return a [java.util.Set] object.
     */
    val dataTypeNames: Set<String>
        get() = map.keys

    val integers: List<AnyInt>
        get() = getIntegers(AnyInt::class.java)

    val signedIntegers: List<AnyInt>
        get() = getIntegers(AnySignedInt::class.java)

    val unSignedIntegers: List<AnyInt>
        get() = getIntegers(AnyUnsignedInt::class.java)

    init {
        add(AnyBit.BOOL)
        add(AnyBit.LWORD)
        add(AnyBit.WORD)
        add(AnyBit.DWORD)

        add(SINT)
        add(INT)
        add(DINT)
        add(LINT)

        add(USINT)
        add(UINT)
        add(UDINT)
        add(ULINT)

        add(AnyReal.LREAL)
        add(AnyReal.REAL)

        add(IECString.STRING_8BIT)
        add(IECString.STRING_16BIT)

        add(TimeType.TIME_TYPE)

        add(AnyDate.DATE)
        add(AnyDate.DATE_AND_TIME)
        add(AnyDate.TIME_OF_DAY)

        map["TOD"] = AnyDate.TIME_OF_DAY
        map["DT"] = AnyDate.DATE_AND_TIME
        map["T"] = TimeType.TIME_TYPE

        map["VOID"] = AnyReference.ANY_REF
    }

    internal fun add(any: AnyDt) {
        map[any.getName()] = any
        map[any.getName().replace("_", "")] = any
    }

    /**
     *
     * getDataType.
     *
     * @param name a [java.lang.String] object.
     * @return a [edu.kit.iti.formal.automation.datatypes.AnyDt] object.
     */
    fun getDataType(name: String): AnyDt {
        return map[name]
    }

    fun getIntegers(anyIntClass: Class<out AnyInt>): List<AnyInt> {
        val list = get<out AnyInt>(anyIntClass)
        list.sort(Comparator.comparingInt<AnyInt> { o -> o.bitLength })
        return list
    }

    private operator fun <T : AnyDt> get(anyClazz: Class<T>): List<T> {
        return map.values.stream().filter { a -> anyClazz.isAssignableFrom(a.javaClass) }
                .collect<List<AnyDt>, Any>(Collectors.toList()) as List<T>
    }

    fun findSuitableInteger(s: BigInteger, signed: Boolean): AnyInt {
        return findSuitableInteger(s,
                if (signed)
                    DataTypes.signedIntegers
                else
                    DataTypes.unSignedIntegers
        )
    }

    @JvmOverloads
    fun findSuitableInteger(s: BigInteger, integerTypes: Iterable<AnyInt> = integers): AnyInt {
        if (s == BigInteger.ZERO) return INT

        for (anyInt in integerTypes) {
            if (s.compareTo(anyInt.upperBound) < 0 && anyInt.lowerBound.compareTo(s) < 0) {
                return anyInt
            }
        }
        throw IllegalStateException("integer literal too big with : $s")
    }


}
