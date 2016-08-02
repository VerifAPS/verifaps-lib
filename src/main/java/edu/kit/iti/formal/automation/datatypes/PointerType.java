package edu.kit.iti.formal.automation.datatypes;

/**
 * Created by weigl on 01.08.16.
 */
public class PointerType extends Any {
    Any of;

    public PointerType(Any dataType) {
        of = dataType;
    }

    @Override
    public String toString() {
        return of + "^";
    }

    @Override
    public String repr(Object obj) {
        return "n/a";
    }
}
