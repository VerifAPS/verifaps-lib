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
import java.util.Optional

/**
 *
 * AnySignedInt class.
 *
 * @author weigl
 * @version $Id: $Id
 */
abstract class AnySignedInt
/**
 *
 * Constructor for AnySignedInt.
 *
 * @param bits a int.
 */
(bits: Int) : AnyInt(bits, true) {

    override val upperBound: BigInteger
        get() = BigInteger.ONE.shiftLeft(bitLength - 1).subtract(BigInteger.ONE)

    override val lowerBound: BigInteger
        get() = BigInteger.ONE.shiftLeft(bitLength - 1).negate()


    /**
     * {@inheritDoc}
     */
    override fun asSigned(): AnyInt {
        return this
    }

    /**
     * {@inheritDoc}
     */
    override fun isValid(value: Long): Boolean {
        val max = ((2 shl bitLength) - 1).toLong()
        val min = (-(2 shl bitLength)).toLong()
        return value <= max && value >= min
    }

    class Arbitrary(bitLength: Int) : AnySignedInt(bitLength) {

        override fun next(): Optional<AnyInt> {
            return Optional.empty()
        }

        override fun asUnsgined(): AnyUnsignedInt {
            return AnyUnsignedInt.Arbitrary(bitLength)
        }
    }
}
