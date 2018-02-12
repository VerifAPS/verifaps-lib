package edu.kit.iti.formal.automation.datatypes;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.values.TimeValue;

/**
 * <p>TimeType class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class TimeType extends Any {
    /** Constant <code>TIME_TYPE</code> */
    public static final TimeType TIME_TYPE = new TimeType();
    public static final TimeType LTIME_TYPE = new TimeType();

    /**
     * <p>Constructor for TimeType.</p>
     */
    public TimeType() {
        super("TIME");
    }

    /** {@inheritDoc} */
    @Override
    public String repr(Object obj) {
        TimeValue time = (TimeValue) obj;
        StringTimeBuilder stb = new StringTimeBuilder();
        stb.add(time.getDays(), "d");
        stb.add(time.getHours(), "h");
        stb.add(time.getMinutes(), "m");
        stb.add(time.getSeconds(), "s");
        stb.add(time.getMilliseconds(), "ms");
        return stb.sb.toString();
    /**
     * <p>add.</p>
     *
     * @param value a double.
     * @param unit a {@link java.lang.String} object.
     */
    }

    /** {@inheritDoc} */
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
