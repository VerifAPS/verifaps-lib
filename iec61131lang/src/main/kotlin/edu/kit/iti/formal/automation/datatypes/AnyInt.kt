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
 * Abstract AnyInt class.
 *
 * @author weigl
 * @version $Id: $Id
 */
abstract class AnyInt : AnyNum {
    /**
     *
     * Getter for the field `bitLength`.
     *
     * @return a int.
     */
    /**
     *
     * Setter for the field `bitLength`.
     *
     * @param bitLength a int.
     */
    var bitLength = 0
    /**
     *
     * isSigned.
     *
     * @return a boolean.
     */
    /**
     *
     * Setter for the field `signed`.
     *
     * @param signed a boolean.
     */
    var isSigned = false

    abstract val upperBound: BigInteger

    abstract val lowerBound: BigInteger

    /**
     *
     * Constructor for AnyInt.
     *
     * @param bitLength a int.
     */
    constructor(bitLength: Int) {
        this.bitLength = bitLength
    }

    /**
     *
     * Constructor for AnyInt.
     *
     * @param bitLength a int.
     * @param signed    a boolean.
     */
    constructor(bitLength: Int, signed: Boolean) {
        this.bitLength = bitLength
        this.isSigned = signed
    }

    /**
     * {@inheritDoc}
     */
    override fun repr(obj: Any): String {
        return javaClass.getSimpleName().toUpperCase() + "#" + obj
    }

    /**
     *
     * next.
     *
     * @return a [edu.kit.iti.formal.automation.datatypes.AnyInt] object.
     */
    abstract operator fun next(): Optional<AnyInt>

    /**
     *
     * asUnsgined.
     *
     * @return a [AnyUnsignedInt] object.
     */
    abstract fun asUnsgined(): AnyUnsignedInt

    /**
     *
     * asSigned.
     *
     * @return a [edu.kit.iti.formal.automation.datatypes.AnyInt] object.
     */
    abstract fun asSigned(): AnyInt


    /**
     *
     * isValid.
     *
     * @param value a long.
     * @return a boolean.
     */
    abstract fun isValid(value: Long): Boolean

    /**
     * {@inheritDoc}
     */
    override fun toString(): String {
        return if (name.isEmpty())
            (if (isSigned) "" else "U") + "INT(" + bitLength + ")"
        else
            name
    }

    /**
     * {@inheritDoc}
     */
    override fun equals(o: Any?): Boolean {
        if (this === o) return true
        if (o !is AnyInt) return false

        val anyInt = o as AnyInt?

        return if (bitLength != anyInt!!.bitLength) false else isSigned == anyInt.isSigned

    }

    /**
     * {@inheritDoc}
     */
    override fun hashCode(): Int {
        var result = bitLength
        result = 31 * result + if (isSigned) 1 else 0
        return result
    }


    /**
     * {@inheritDoc}
     */
    override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
        return visitor.visit(this)
    }

    companion object {

        /**
         *
         * getDataTypeFor.
         *
         * @param number   a int.
         * @param unsigned a boolean.
         * @return a [edu.kit.iti.formal.automation.datatypes.AnyInt] object.
         */
        fun getDataTypeFor(number: Int, unsigned: Boolean): AnyInt {
            val values: Array<AnyInt>
            if (unsigned)
                values = arrayOf(DataTypes.USINT, DataTypes.UINT, DataTypes.ULINT, DataTypes.UDINT)
            else
                values = arrayOf(DataTypes.SINT, DataTypes.INT, DataTypes.LINT, DataTypes.DINT)

            val bits = Math.ceil(Math.log(number.toDouble()) / Math.log(2.0)).toInt()

            for (candidate in values) {
                if (candidate.bitLength >= bits)
                    return candidate
            }

            if (bits < 0)
                return if (unsigned) DataTypes.USINT else DataTypes.SINT

            /*for (AnyInt bit : values)
            if (bit.getBitLength() >= bits)
                return bit;*/

            return if (unsigned)
                AnyUnsignedInt.Arbitrary(bits)
            else
                AnySignedInt.Arbitrary(bits)
        }
    }

}
