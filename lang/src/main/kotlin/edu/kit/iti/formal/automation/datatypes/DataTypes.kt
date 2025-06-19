/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.automation.datatypes

import java.math.BigInteger
import java.util.*

/**
 *
 * DataTypes class.
 *
 * @author Alexander Weigl (25.06.2014)
 * @version 1
 */
object DataTypes {
    internal var map = HashMap<String, AnyDt>()

    val dataTypeNames: Set<String>
        get() = map.keys

    val integers: Array<AnyInt>
        get() = signedIntegers + unSignedIntegers

    val signedIntegers: Array<AnyInt>
        get() = arrayOf(INT, SINT, DINT, LINT)

    val unSignedIntegers: Array<AnyInt>
        get() = arrayOf(UINT, USINT, UDINT, ULINT)

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

        add(IECString.STRING)
        add(IECString.WSTRING)

        add(TimeType.TIME_TYPE)

        add(AnyDate.DATE)
        add(AnyDate.DATE_AND_TIME)
        add(AnyDate.TIME_OF_DAY)

        map["TOD"] = AnyDate.TIME_OF_DAY
        map["DT"] = AnyDate.DATE_AND_TIME
        map["T"] = TimeType.TIME_TYPE
        map["VOID"] = ReferenceDt.ANY_REF
    }

    internal fun add(any: AnyDt) {
        map[any.name] = any
        map[any.name.replace("_", "")] = any
    }

    fun getDataType(name: String): AnyDt? = map[name]

    /*
    fun getIntegers(anyIntClass: Class<out AnyInt>): List<AnyInt> {
        val list = get(anyIntClass)
        list.sort(Comparator.comparingInt<AnyInt> { o -> o.bitLength })
        return list
    }
     */

    private operator fun <T : AnyDt> get(anyClazz: Class<T>) = map.values.filter {
        anyClazz.isAssignableFrom(it.javaClass)
    }

    fun findSuitableInteger(s: BigInteger, signed: Boolean): AnyInt = findSuitableInteger(
        s,
        if (signed) {
            DataTypes.signedIntegers
        } else {
            DataTypes.unSignedIntegers
        },
    )

    fun findSuitableInteger(s: BigInteger, integerTypes: Array<AnyInt> = integers): AnyInt {
        if (s == BigInteger.ZERO) return INT

        for (anyInt in integerTypes) {
            if (s.compareTo(anyInt.upperBound) < 0 && anyInt.lowerBound.compareTo(s) < 0) {
                return anyInt
            }
        }
        throw IllegalStateException("integer literal too big with : $s")
    }
}