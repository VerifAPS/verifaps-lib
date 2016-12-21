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

import edu.kit.iti.formal.automation.datatypes.values.DateValue;
import edu.kit.iti.formal.automation.datatypes.values.DateAndTimeValue;
import edu.kit.iti.formal.automation.datatypes.values.TimeOfDayValue;

/**
 * <p>Abstract AnyDate class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public abstract class AnyDate extends Any {
    public static class Date extends AnyDate {
        @Override
        public String repr(Object obj) {
            DateValue dt = (DateValue) obj;
            return String.format("DATE#%4d-%2d-%2d",
                    dt.getYear(), dt.getMonth(), dt.getDay());
        }

        @Override
        public <T> T accept(DataTypeVisitor<T> visitor) {
            return visitor.visit(this);
        }
    }

    public static class TimeOfDay extends AnyDate {
        @Override
        public String repr(Object obj) {
            TimeOfDayValue dt = (TimeOfDayValue) obj;
            return String.format("TOD#%2d:%2d:%2d.%3d",
                    dt.getHours(), dt.getMinutes(), dt.getSeconds(), dt.getMillieseconds());
        }


        @Override
        public <T> T accept(DataTypeVisitor<T> visitor) {
            return visitor.visit(this);
        }
    }

    public static class DateAndTime extends AnyDate {
        @Override
        public String repr(Object obj) {
            DateAndTimeValue dt = (DateAndTimeValue) obj;
            return String.format("DT#%4d-%2d-%2d-%2d:%2d:%2d.%3d",
                    dt.getYear(), dt.getMonth(), dt.getDay(), dt.getHours(), dt.getMinutes(), dt.getSeconds(), dt.getMillieSeconds());
        }

        @Override
        public <T> T accept(DataTypeVisitor<T> visitor) {
            return visitor.visit(this);
        }
    }

    /** Constant <code>DATE</code> */
    public static final Date DATE = new Date();
    /** Constant <code>TIME_OF_DAY</code> */
    public static final TimeOfDay TIME_OF_DAY = new TimeOfDay();
    /** Constant <code>DATE_AND_TIME</code> */
    public static final DateAndTime DATE_AND_TIME = new DateAndTime();
}
