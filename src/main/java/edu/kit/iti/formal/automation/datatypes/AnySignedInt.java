package edu.kit.iti.formal.automation.datatypes;

public class AnySignedInt extends AnyInt {
    public AnySignedInt(int bitLength, boolean signed) {
        super(bitLength, signed);
    }

    public AnySignedInt(int bits) {
        super(bits);
    }

    @Override
    public AnyInt asSigned() {
        return this;
    }

    @Override
    public AnyUInt asUnsgined() {
        return new AnyUInt(bitLength);
    }

    @Override
    public AnyInt next() {
        return null;//TODO
    }

    @Override
    public boolean isValid(long value) {
        long max = (2 << bitLength) - 1;
        long min = -(2 << bitLength);
        return value <= max && value >= min;
    }
}