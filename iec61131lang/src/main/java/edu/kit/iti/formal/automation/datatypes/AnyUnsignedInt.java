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

/**
 * <p>AnyUInt class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class AnyUInt extends AnyInt {
    /**
     * <p>Constructor for AnyUInt.</p>
     *
     * @param bitLength a int.
     */
    public AnyUInt(int bitLength) {
        super(bitLength, false);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AnyInt asSigned() {
        return new AnySignedInt(bitLength);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AnyUInt asUnsgined() {
        return this;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AnyInt next() {
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isValid(long value) {
        return value < (1 << bitLength);
    }

    @Override
    public <T> T accept(DataTypeVisitor<T> visitor) {
        return visitor.visit(DataTypes.SINT);
    }
}
