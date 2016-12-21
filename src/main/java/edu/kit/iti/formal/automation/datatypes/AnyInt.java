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
 * <p>Abstract AnyInt class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public abstract class AnyInt extends AnyNum {
    /** Constant <code>DEFAULT</code> */
    public static final Integer DEFAULT = 0;
    /** Constant <code>SINT</code> */
    public static final SInt SINT = new SInt();
    /** Constant <code>USINT</code> */
    public static final USInt USINT = new USInt();
    /** Constant <code>INT</code> */
    public static final Int INT = new Int();
    /** Constant <code>UINT</code> */
    public static final UInt UINT = new UInt();
    /** Constant <code>UDINT</code> */
    public static final UDInt UDINT = new UDInt();
    /** Constant <code>DINT</code> */
    public static final DInt DINT = new DInt();
    /** Constant <code>ULINT</code> */
    public static final ULInt ULINT = new ULInt();
    /** Constant <code>LINT</code> */
    public static final LInt LINT = new LInt();

    protected int bitLength = 0;

    protected boolean signed = false;

    /**
     * <p>Constructor for AnyInt.</p>
     *
     * @param bitLength a int.
     */
    public AnyInt(int bitLength) {
        this.bitLength = bitLength;
    }

    /**
     * <p>Constructor for AnyInt.</p>
     *
     * @param bitLength a int.
     * @param signed a boolean.
     */
    public AnyInt(int bitLength, boolean signed) {
        this.bitLength = bitLength;
        this.signed = signed;
    }

    /** {@inheritDoc} */
    @Override
    public String repr(Object obj) {
        return getClass().getSimpleName().toUpperCase() + "#" + obj;
    }


    /**
     * <p>Getter for the field <code>bitLength</code>.</p>
     *
     * @return a int.
     */
    public int getBitLength() {
        return bitLength;
    }

    /**
     * <p>Setter for the field <code>bitLength</code>.</p>
     *
     * @param bitLength a int.
     */
    public void setBitLength(int bitLength) {
        this.bitLength = bitLength;
    }

    /**
     * <p>isSigned.</p>
     *
     * @return a boolean.
     */
    public boolean isSigned() {
        return signed;
    }

    /**
     * <p>Setter for the field <code>signed</code>.</p>
     *
     * @param signed a boolean.
     */
    public void setSigned(boolean signed) {
        this.signed = signed;
    }

    /**
     * <p>getDataTypeFor.</p>
     *
     * @param number a int.
     * @param unsigned a boolean.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.AnyInt} object.
     */
    public static AnyInt getDataTypeFor(int number, boolean unsigned) {
        AnyInt[] values;
        if (unsigned)
            values = new AnyInt[]{USINT, UINT, ULINT, UDINT};
        else
            values = new AnyInt[]{SINT, INT, LINT, DINT};

        int bits = (int) Math.ceil(Math.log(number) / Math.log(2));

        if (bits < 0)
            return unsigned ? USINT : SINT;

        /*for (AnyInt bit : values)
            if (bit.getBitLength() >= bits)
                return bit;*/

        if (unsigned)
            return new AnyUInt(bits) {
                @Override
                public String getName() {
                    return "UINT";
                }
            };
        else
            return new AnySignedInt(bits) {
                @Override
                public String getName() {
                    return "INT[" + bitLength + "]";
                }
            };
    }

    /**
     * <p>next.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.datatypes.AnyInt} object.
     */
    public abstract AnyInt next();

    /**
     * <p>asUnsgined.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.datatypes.AnyUInt} object.
     */
    public abstract AnyUInt asUnsgined();

    /**
     * <p>asSigned.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.datatypes.AnyInt} object.
     */
    public abstract AnyInt asSigned();


    /**
     * <p>isValid.</p>
     *
     * @param value a long.
     * @return a boolean.
     */
    public abstract boolean isValid(long value);

    /** {@inheritDoc} */
    @Override
    public String toString() {
        if (name.isEmpty())
            return (signed ? "" : "U") + "INT(" + bitLength + ")";
        else
            return name;
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof AnyInt)) return false;

        AnyInt anyInt = (AnyInt) o;

        if (getBitLength() != anyInt.getBitLength()) return false;
        return isSigned() == anyInt.isSigned();

    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        int result = bitLength;
        result = 31 * result + (signed ? 1 : 0);
        return result;
    }


    /** {@inheritDoc} */
    @Override
    public <T> T accept(DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
