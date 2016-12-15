package edu.kit.iti.formal.automation.datatypes;

import edu.kit.iti.formal.automation.datatypes.values.TimeValue;

public class TimeType extends Any {
    public static final TimeType TIME_TYPE = new TimeType();

    public TimeType() {
        super("TIME");
    }

    @Override
    public String repr(Object obj) {
        TimeValue time = (TimeValue) obj;
        StringTimeBuilder stb = new StringTimeBuilder();
        stb.add(time.getDays(), "d");
        stb.add(time.getHours(), "h");
        stb.add(time.getMinutes(), "m");
        stb.add(time.getSeconds(), "s");
        stb.add(time.getMillieseconds(), "ms");
        return stb.sb.toString();
    }

    @Override
    public <T> T accept(DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }
}

class StringTimeBuilder {
    public StringBuilder sb = new StringBuilder("TIME#");

    public void add(double value, String unit) {
        if (value != 0) {
            sb.append(value).append(unit);
        }
    }
}