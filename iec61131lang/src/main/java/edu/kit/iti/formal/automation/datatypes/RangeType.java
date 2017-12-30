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

import lombok.Getter;
import lombok.Setter;

import java.math.BigInteger;

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
@Getter
@Setter
public class RangeType extends AnyInt {
    private int bottom;
    private int top;
    private AnyInt base;

    /**
     * <p>Constructor for RangeType.</p>
     *
     * @param bottom a long.
     * @param top    a long.
     * @param base   a {@link edu.kit.iti.formal.automation.datatypes.AnyInt} object.
     */
    public RangeType(int bottom, int top, AnyInt base) {
        super(base.bitLength, base.signed);
        this.bottom = bottom;
        this.top = top;
        this.base = base;
    }

    public RangeType(String name, int bottom, int top, AnyInt base) {
        super(base.bitLength, base.signed);
        this.name = name;
        this.bottom = bottom;
        this.top = top;
        this.base = base;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String repr(Object obj) {
        return base.repr(obj);
    }

    @Override
    public AnyInt next() {
        return this;
    }

    @Override
    public AnyUnsignedInt asUnsgined() {
        return null;
    }

    @Override
    public AnyInt asSigned() {
        return null;
    }

    @Override
    public boolean isValid(long value) {
        return bottom <= value && value <= top;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public <T> T accept(DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public BigInteger getUpperBound() {
        return BigInteger.valueOf(top);
    }

    @Override
    public BigInteger getLowerBound() {
        return BigInteger.valueOf(bottom);
    }
}
