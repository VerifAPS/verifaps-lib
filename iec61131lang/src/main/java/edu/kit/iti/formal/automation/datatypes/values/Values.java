package edu.kit.iti.formal.automation.datatypes.values;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.datatypes.*;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (25.06.17)
 */
public abstract class Values {

    public static class VClass extends Value<ClassDataType, Map<String, Value>> {
        public VClass(ClassDataType dataType, Map<String, Value> value) {
            super(dataType, value);
        }
    }

    public static class VAnyInt extends Value<AnyInt, BigInteger> {
        public VAnyInt(AnyInt dataType, BigInteger value) {
            super(dataType, value);
        }
    }

    public static class VAnyReal extends Value<AnyReal, BigDecimal> {
        public VAnyReal(AnyReal dataType, BigDecimal value) {
            super(dataType, value);
        }
    }

    public static class VAnyBit extends Value<AnyBit, Bits> {
        public VAnyBit(AnyBit dataType, Bits value) {
            super(dataType, value);
        }
    }

    public static class VBool extends Value<AnyBit.Bool, Boolean> {
        public static final Value TRUE = new VBool(AnyBit.BOOL, true);
        public static final Value FALSE = new VBool(AnyBit.BOOL, false);

        public VBool(AnyBit.Bool dataType, Boolean value) {
            super(dataType, value);
        }
    }

    public static class VIECString extends Value<IECString, String> {
        public VIECString(IECString dataType, String value) {
            super(dataType, value);
        }
    }

    public static class VDate extends Value<AnyDate.Date, DateData> {
        public VDate(AnyDate.Date dataType, DateData value) {
            super(dataType, value);
        }
    }

    public static class VDateAndTime extends Value<AnyDate.DateAndTime, DateAndTimeData> {
        public VDateAndTime(AnyDate.DateAndTime dataType, DateAndTimeData value) {
            super(dataType, value);
        }
    }

    public static class VTimeOfDay extends Value<AnyDate.TimeOfDay, TimeofDayData> {
        public VTimeOfDay(AnyDate.TimeOfDay dataType, TimeofDayData value) {
            super(dataType, value);
        }
    }

    public static class VAnyEnum extends Value<EnumerateType, String> {
        public VAnyEnum(EnumerateType enumerateType, String value) {
            super(enumerateType, value);
        }
    }

    public static class VToD extends Value<AnyDate.TimeOfDay, TimeofDayData> {
        public VToD(AnyDate.TimeOfDay timeOfDay, TimeofDayData t) {
            super(timeOfDay, t);
        }
    }
}
