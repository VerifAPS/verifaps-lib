package edu.kit.iti.formal.automation.datatypes;

public abstract class AnyInt extends AnyNum {
    public static final Integer DEFAULT = 0;
    public static final SInt SINT = new SInt();
    public static final USInt USINT = new USInt();
    public static final Int INT = new Int();
    public static final UInt UINT = new UInt();
    public static final UDInt UDINT = new UDInt();
    public static final DInt DINT = new DInt();
    public static final ULInt ULINT = new ULInt();
    public static final LInt LINT = new LInt();

    protected int bitLength = 0;

    protected boolean signed = false;

    public AnyInt(int bitLength) {
        this.bitLength = bitLength;
    }

    public AnyInt(int bitLength, boolean signed) {
        this.bitLength = bitLength;
        this.signed = signed;
    }

    @Override
    public String repr(Object obj) {
        return getClass().getSimpleName().toUpperCase() + "#" + obj;
    }


    public int getBitLength() {
        return bitLength;
    }

    public void setBitLength(int bitLength) {
        this.bitLength = bitLength;
    }

    public boolean isSigned() {
        return signed;
    }

    public void setSigned(boolean signed) {
        this.signed = signed;
    }

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
     * @return
     */
    public abstract AnyInt next();

    /**
     * @return
     */
    public abstract AnyUInt asUnsgined();

    /**
     * @return
     */
    public abstract AnyInt asSigned();


    /**
     * @param value
     * @return
     */
    public abstract boolean isValid(long value);

    @Override
    public String toString() {
        if (name.isEmpty())
            return (signed ? "" : "U") + "INT(" + bitLength + ")";
        else
            return name;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof AnyInt)) return false;

        AnyInt anyInt = (AnyInt) o;

        if (bitLength != anyInt.bitLength) return false;
        return signed == anyInt.signed;

    }

    @Override
    public int hashCode() {
        int result = bitLength;
        result = 31 * result + (signed ? 1 : 0);
        return result;
    }


    @Override
    public <T> T accept(DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }
}