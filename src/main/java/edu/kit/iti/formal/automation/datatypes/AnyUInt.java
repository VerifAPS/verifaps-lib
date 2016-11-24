package edu.kit.iti.formal.automation.datatypes;

public class AnyUInt extends AnyInt {
    public AnyUInt(int bitLength) {
        super(bitLength, false);
    }

    @Override
    public AnyInt asSigned() {
        return new AnySignedInt(bitLength);
    }

    @Override
    public AnyUInt asUnsgined() {
        return this;
    }

    @Override
    public AnyInt next() {
        return null;
    }

    @Override
    public boolean isValid(long value) {
        return value < (1 << bitLength);
    }
}