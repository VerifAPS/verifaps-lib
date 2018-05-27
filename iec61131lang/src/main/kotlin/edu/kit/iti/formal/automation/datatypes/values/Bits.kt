package edu.kit.iti.formal.automation.datatypes.values

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

import lombok.*

/**
 * Created by weigl on 11.06.14.
 * Immutable
 *
 * @author weigl
 * @version $Id: $Id
 */
@Data
class Bits
/**
 *
 * Constructor for Bits.
 *
 * @param register a long.
 * @param nbits a long.
 */
(register: Long, val nbits: Long) {
    /**
     *
     * Getter for the field `register`.
     *
     * @return a long.
     */
    /**
     *
     * Setter for the field `register`.
     *
     * @param register a long.
     */
    var register: Long = 0

    /**
     *
     * Constructor for Bits.
     *
     * @param nbits a long.
     */
    constructor(nbits: Long) : this(0, nbits) {}

    init {
        this.register = register and allMask() // trunc
    }

    private fun allMask(): Long {
        return if (nbits == 64L) {
            -1L
        } else {
            (1L shl nbits) - 1
        }
    }

    /**
     *
     * shl.
     *
     * @param n a int.
     * @return a [edu.kit.iti.formal.automation.datatypes.values.Bits] object.
     */
    fun shl(n: Int): Bits {
        return Bits(register shl n, nbits)
    }

    /**
     *
     * shr.
     *
     * @param n a int.
     * @return a [edu.kit.iti.formal.automation.datatypes.values.Bits] object.
     */
    fun shr(n: Int): Bits {
        return Bits(register.ushr(n), nbits)
    }


    /**
     *
     * rol.
     *
     * @param n a int.
     * @return a [edu.kit.iti.formal.automation.datatypes.values.Bits] object.
     */
    fun rol(n: Int): Bits {
        assert(n <= nbits)

        if (n.toLong() == nbits) {
            return this
        }


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


    /**
     *
     * and.
     *
     * @param other a [edu.kit.iti.formal.automation.datatypes.values.Bits] object.
     * @return a [edu.kit.iti.formal.automation.datatypes.values.Bits] object.
     */
    fun and(other: Bits): Bits {
        return Bits(register and other.register, nbits)
    }

    /**
     *
     * or.
     *
     * @param other a [edu.kit.iti.formal.automation.datatypes.values.Bits] object.
     * @return a [edu.kit.iti.formal.automation.datatypes.values.Bits] object.
     */
    fun or(other: Bits): Bits {
        return Bits(register or other.register, nbits)
    }

    /**
     *
     * xor.
     *
     * @param other a [edu.kit.iti.formal.automation.datatypes.values.Bits] object.
     * @return a [edu.kit.iti.formal.automation.datatypes.values.Bits] object.
     */
    fun xor(other: Bits): Bits {
        return Bits(register xor other.register, nbits)
    }
}
