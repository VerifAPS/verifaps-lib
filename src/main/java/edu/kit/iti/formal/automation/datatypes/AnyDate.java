package edu.kit.iti.formal.automation.datatypes;

import edu.kit.iti.formal.automation.datatypes.values.DateAndTimeValue;
import edu.kit.iti.formal.automation.datatypes.values.DateValue;
import edu.kit.iti.formal.automation.datatypes.values.TimeOfDayValue;

public abstract class AnyDate extends Any {
    public static class Date extends AnyDate {
        @Override
        public String repr(Object obj) {
            DateValue dt = (DateValue) obj;
            return String.format("DATE#%4d-%2d-%2d",
                    dt.getYear(), dt.getMonth(), dt.getDay());
        }
    }

    public static class TimeOfDay extends AnyDate {
        @Override
        public String repr(Object obj) {
            TimeOfDayValue dt = (TimeOfDayValue) obj;
            return String.format("TOD#%2d:%2d:%2d.%3d",
                    dt.getHours(), dt.getMinutes(), dt.getSeconds(), dt.getMillieseconds());
        }
    }

    public static class DateAndTime extends AnyDate {
        @Override
        public String repr(Object obj) {
            DateAndTimeValue dt = (DateAndTimeValue) obj;
            return String.format("DT#%4d-%2d-%2d-%2d:%2d:%2d.%3d",
                    dt.getYear(), dt.getMonth(), dt.getDay(), dt.getHours(), dt.getMinutes(), dt.getSeconds(), dt.getMillieSeconds());
        }
    }

    public static final Date DATE = new Date();
    public static final TimeOfDay TIME_OF_DAY = new TimeOfDay();
    public static final DateAndTime DATE_AND_TIME = new DateAndTime();
}