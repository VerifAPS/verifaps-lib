package edu.kit.iti.formal.automation.datatypes;

public final class LInt extends AnySignedInt {
    @Override
    public AnyInt next() {
        return LINT;
    }

    public LInt() {
        super(64);
    }
}