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

abstract class AnyUnsignedInt(bitLength: Int) : AnyInt(bitLength, false) {

    override val upperBound: BigInteger
        get() = BigInteger.ONE.shiftLeft(bitLength)

    override val lowerBound: BigInteger
        get() = BigInteger.ZERO

    override fun asUnsgined(): AnyUnsignedInt {
        return this
    }

    override fun isValid(value: Long): Boolean {
        return value < 1 shl bitLength
    }

    override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
        return visitor.visit(this)
    }

    class Arbitrary(bitLength: Int) : AnyUnsignedInt(bitLength) {

        override fun next(): Optional<AnyInt> {
            return Optional.empty()
        }

        override fun asSigned(): AnyInt {
            return AnySignedInt.Arbitrary(bitLength)
        }
    }
}
