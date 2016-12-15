package edu.kit.iti.formal.automation.datatypes;

import edu.kit.iti.formal.automation.datatypes.values.Bits;

/**
 * Created by weigl on 10.06.14.
 */
public abstract class AnyBit extends Any {
    public final static Bool BOOL = new Bool();
    public final static Byte BYTE = new Byte();
    public final static Word WORD = new Word();
    public final static DWord DWORD = new DWord();
    public final static LWord LWORD = new LWord();


    protected int bitLength;

    private AnyBit(int bitLength) {
        this.bitLength = bitLength;
    }

    public int getBitLength() {
        return bitLength;
    }



    @Override
    public <T> T accept(DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }

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
