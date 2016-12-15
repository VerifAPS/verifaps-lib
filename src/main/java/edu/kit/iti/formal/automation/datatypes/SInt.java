package edu.kit.iti.formal.automation.datatypes;

public final class SInt extends AnySignedInt {
    public SInt() {
        super(8, true);
    }

    @Override
    public AnyInt next() {
        return INT;
    }

}