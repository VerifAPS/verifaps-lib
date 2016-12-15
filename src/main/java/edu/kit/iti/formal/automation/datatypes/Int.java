package edu.kit.iti.formal.automation.datatypes;

public final class Int extends AnySignedInt {
    @Override
    public AnyInt next() {
        return DINT;
    }

    public Int() {
        super(16);
    }
}