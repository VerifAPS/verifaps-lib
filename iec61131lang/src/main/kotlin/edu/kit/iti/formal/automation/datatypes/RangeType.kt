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

import lombok.Getter
import lombok.Setter

import java.math.BigInteger
import java.util.Optional

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
@Getter
@Setter
class RangeType : AnyInt {
    private var bottom: Int = 0
    private var top: Int = 0
    private var base: AnyInt? = null

    override val upperBound: BigInteger
        get() = BigInteger.valueOf(top.toLong())

    override val lowerBound: BigInteger
        get() = BigInteger.valueOf(bottom.toLong())

    /**
     *
     * Constructor for RangeType.
     *
     * @param bottom a long.
     * @param top    a long.
     * @param base   a [edu.kit.iti.formal.automation.datatypes.AnyInt] object.
     */
    constructor(bottom: Int, top: Int, base: AnyInt) : super(base.bitLength, base.isSigned) {
        this.bottom = bottom
        this.top = top
        this.base = base
    }

    constructor(name: String, bottom: Int, top: Int, base: AnyInt) : super(base.bitLength, base.isSigned) {
        this.name = name
        this.bottom = bottom
        this.top = top
        this.base = base
    }

    /**
     * {@inheritDoc}
     */
    override fun repr(obj: Any): String {
        return base!!.repr(obj)
    }

    override fun next(): Optional<AnyInt> {
        return Optional.empty()
    }

    override fun asUnsgined(): AnyUnsignedInt? {
        return null
    }

    override fun asSigned(): AnyInt? {
        return null
    }

    override fun isValid(value: Long): Boolean {
        return bottom <= value && value <= top
    }

    /**
     * {@inheritDoc}
     */
    override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
        return visitor.visit(this)
    }
}
