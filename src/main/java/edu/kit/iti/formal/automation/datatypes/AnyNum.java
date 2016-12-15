package edu.kit.iti.formal.automation.datatypes;

/**
 * Created by weigl on 10.06.14.
 */
public class AnyNum extends Any {
    public static final Any ANY_NUM = new AnyNum();

    @Override
    public String repr(Object obj) {
        throw new IllegalStateException("No repr for AnyNum");
    }

    @Override
    public String toString() {
        return "ANY_NUM";
    }


    @Override
    public <T> T accept(DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
