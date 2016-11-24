package edu.kit.iti.formal.automation.datatypes;

public final class SInt extends AnySignedInt {
    public SInt() {
        super(8, false);
    }

    @Override
    public AnyInt next() {
        return INT;
    }

}