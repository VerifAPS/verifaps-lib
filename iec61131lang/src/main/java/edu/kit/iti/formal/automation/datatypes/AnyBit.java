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

import edu.kit.iti.formal.automation.datatypes.values.Bits;

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public abstract class AnyBit extends Any {
    /** Constant <code>BOOL</code> */
    public final static Bool BOOL = new Bool();
    /** Constant <code>BYTE</code> */
    public final static Byte BYTE = new Byte();
    /** Constant <code>WORD</code> */
    public final static Word WORD = new Word();
    /** Constant <code>DWORD</code> */
    public final static DWord DWORD = new DWord();
    /** Constant <code>LWORD</code> */
    public final static LWord LWORD = new LWord();


    protected int bitLength;

    private AnyBit(int bitLength) {
        this.bitLength = bitLength;
    }

    /**
     * <p>Getter for the field <code>bitLength</code>.</p>
     *
     * @return a int.
     */
    public int getBitLength() {
        return bitLength;
    }



    /** {@inheritDoc} */
    @Override
    public <T> T accept(DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }

    /** {@inheritDoc} */
    @Override
    public String repr(Object obj) {
        if (obj instanceof Bits) {
            if (((Bits) obj).getRegister() > 0)
                return getClass().getName().toUpperCase() + "#2#"
                        + Long.toBinaryString(((Bits) obj).getRegister());
        }
        return "";
    }

    public final static class Bool extends AnyBit {
        public Bool() {
            super(1);
        }

        @Override
        public String repr(Object obj) {
            if (obj instanceof Bits) {
                if (((Bits) obj).getRegister() > 0)
                    return "TRUE";
            }

            if (obj instanceof Boolean) {
                if ((Boolean) obj)
                    return "TRUE";
            }
            return "FALSE";
        }
    }

    public final static class Byte extends AnyBit {
        public Byte() {
            super(8);
        }
    }

    public final static class Word extends AnyBit {
        public Word() {
            super(16);
        }
    }

    public final static class DWord extends AnyBit {
        public DWord() {
            super(32);
        }
    }

    public final static class LWord extends AnyBit {
        public LWord() {
            super(64);
        }
    }
}
