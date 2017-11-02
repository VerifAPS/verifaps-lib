package edu.kit.iti.formal.automation.datatypes.values;

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

import edu.kit.iti.formal.automation.datatypes.AnyDate;
import edu.kit.iti.formal.automation.sfclang.Utils;
import lombok.*;

import java.util.function.Function;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * <p>TimeofDayData class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
@Data
@NoArgsConstructor
public class TimeofDayData {
    private int hours, minutes, seconds, millieseconds;

    public TimeofDayData(int hours, int minutes, int seconds) {
        this.hours = hours;
        this.minutes = minutes;
        this.seconds = seconds;
    }

    public TimeofDayData(int hour, int min, int sec, int ms) {
        this(hour, min, sec);
        millieseconds = ms;
    }

    public static Value<AnyDate.TimeOfDay, TimeofDayData> parse(String tod) {
        Pattern pattern = Pattern.compile(
                "(?<hour>\\d?\\d):(?<min>\\d?\\d)(:(?<sec>\\d?\\d))?(.(?<ms>\\d+))?");
        Utils.Splitted s = Utils.split(tod);
        Matcher matcher = pattern.matcher(s.value().get());
        Function<String, Integer> parseInt = (String key) -> {
            String a = matcher.group(key);
            if (a == null)
                return 0;
            else
                return Integer.parseInt(a);
        };

        if (matcher.matches()) {
            int hour = parseInt.apply("hour");
            int min = parseInt.apply("min");
            int sec = parseInt.apply("sec");
            int ms = parseInt.apply("ms");
            TimeofDayData t = new TimeofDayData(hour, min, sec, ms);
            return new Values.VToD(AnyDate.TIME_OF_DAY, t);
        } else {
            throw new IllegalArgumentException("Given string is not a time of day value.");
        }
    }
}
