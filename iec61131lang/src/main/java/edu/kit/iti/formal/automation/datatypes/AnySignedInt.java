package edu.kit.iti.formal.automation.datatypes;

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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import java.math.BigInteger;

/**
 * <p>AnySignedInt class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class AnySignedInt extends AnyInt {
    /**
     * <p>Constructor for AnySignedInt.</p>
     *
     * @param bits a int.
     */
    public AnySignedInt(int bits) {
        super(bits, true);
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public AnyInt asSigned() {
        return this;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AnyUnsignedInt asUnsgined() {
        return new AnyUnsignedInt(bitLength);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AnyInt next() {
        return null;//TODO
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isValid(long value) {
        long max = (2 << bitLength) - 1;
        long min = -(2 << bitLength);
        return value <= max && value >= min;
    }

    @Override
    public BigInteger getUpperBound() {
        return BigInteger.ONE.shiftLeft(bitLength - 1).subtract(BigInteger.ONE);
    }

    @Override
    public BigInteger getLowerBound() {
        return BigInteger.ONE.shiftLeft(bitLength - 1).negate();
    }
}
