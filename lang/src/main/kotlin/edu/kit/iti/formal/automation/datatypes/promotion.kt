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

fun getPromotion(a: AnyDt, b: AnyDt): AnyDt? = a.accept(PromotionVisitor(b))
infix fun AnyDt.promoteWith(other: AnyDt): AnyDt? = getPromotion(this, other)

class PromotionVisitor(val other: AnyDt) : DataTypeVisitor<AnyDt> {
    override fun defaultVisit(obj: Any) = null
    override fun visit(real: AnyReal): AnyDt? = when (other) {
        is AnyReal ->
            // silent assumption: only REAL and LREAL
            if (real == other) real else AnyReal.LREAL
        is AnyInt -> real
        else -> null
    }

    override fun visit(anyInt: AnyInt): AnyDt? = when (other) {
        is AnyReal -> getPromotion(other, anyInt)
        is AnyInt -> {
            when {
                (anyInt.isSigned && other.isSigned) ->
                    if (anyInt.bitLength >= other.bitLength) anyInt else other
                (!anyInt.isSigned && !other.isSigned) ->
                    if (anyInt.bitLength >= other.bitLength) anyInt else other
                else -> findNext(anyInt, other)
            }
        }
        else -> null
    }

    override fun visit(anyBit: AnyBit): AnyDt? = when (other) {
        is AnyBit ->
            if (anyBit.bitLength >= other.bitLength) anyBit else other
        else -> null
    }

    override fun visit(enumerateType: EnumerateType): AnyDt? = when (other) {
        enumerateType -> enumerateType
        is AnyInt -> getPromotion(AnyInt(enumerateType.bitlength), other)
        else -> null
    }

    override fun visit(string: IECString.STRING): AnyDt? = if (string == other) {
        string
    } else {
        null
    }

    override fun visit(wString: IECString.WSTRING): AnyDt? = if (wString == other) {
        wString
    } else {
        null
    }

    private fun findNext(a: AnyInt, b: AnyInt): AnyInt {
        var (signed, unsigned) = if (a.isSigned) Pair(a, b) else Pair(b, a)
        while (signed.upperBound < unsigned.upperBound) {
            signed = signed.next() ?: break
        }
        return signed
    }
}
