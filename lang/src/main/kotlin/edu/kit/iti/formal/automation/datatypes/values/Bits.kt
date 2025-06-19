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
package edu.kit.iti.formal.automation.datatypes.values

import java.math.BigInteger

/**
 * Created by weigl on 11.06.14.
 * @author weigl
 * @version $Id: $Id
 */
data class Bits(val register: Long = 0, val nbits: Int = 1) {
    private fun allMask() = if (nbits == 64) -1L else (1L shl nbits) - 1

    fun shl(n: Int) = Bits(register shl n, nbits)
    fun shr(n: Int) = Bits(register.ushr(n), nbits)
    fun rol(n: Int): Bits {
        assert(n <= nbits)

        if (n == nbits) return this

        val maskAll = allMask()
        val maskRetain = ((2 shl nbits - n) - 1).toLong()
        val maskLoss = maskRetain.inv() and maskAll

        val loss = register and maskRetain
        val last = loss shr nbits - n
        return Bits(register shl n or last, nbits)
    }

    /**
     *
     * ror.
     *
     * @param n a int.
     * @return a [edu.kit.iti.formal.automation.datatypes.values.Bits] object.
     */
    fun ror(n: Int): Bits {
        val maskAll = allMask()
        val maskLoss = ((2 shl n) - 1).toLong()

        val loss = maskLoss and register
        val first = loss shl n

        return Bits(register.ushr(n) or first, nbits)
    }

    fun and(other: Bits): Bits = Bits(register and other.register, nbits)
    fun or(other: Bits) = Bits(register or other.register, nbits)
    fun xor(other: Bits): Bits = Bits(register xor other.register, nbits)
    fun toBigInt() = BigInteger.valueOf(register)
}