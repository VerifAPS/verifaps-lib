package edu.kit.iti.formal.automation.datatypes;

public final class DInt extends AnySignedInt {
    @Override
    public AnyInt next() {
        return LINT;
    }

    public DInt() {
        super(32, true);
    }
}