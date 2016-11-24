package edu.kit.iti.formal.automation.datatypes;

public final class UInt extends AnyUInt {
    public UInt() {
        super(16);
    }

    @Override
    public AnyInt next() {
        return UDINT;
    }
}
