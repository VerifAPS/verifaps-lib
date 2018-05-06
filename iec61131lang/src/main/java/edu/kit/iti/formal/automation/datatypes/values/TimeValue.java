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

/**
 * Created by weigl on 11.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */

import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.math.BigDecimal;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

@NoArgsConstructor
@AllArgsConstructor
@Data
public class TimeValue {
    public static final int FACTOR_MILLISECONDS = 1;
    public static final int FACTOR_SECONDS = 1000 * FACTOR_MILLISECONDS;
    public static final int FACTOR_MINUTE = 60 * FACTOR_SECONDS;
    public static final int FACTOR_HOUR = 60 * FACTOR_MINUTE;
    public static final int FACTOR_DAY = 24 * FACTOR_HOUR;
    // value in millieseconds
    private BigDecimal internal = BigDecimal.ZERO;

    public TimeValue(String textValue) {
        textValue = textValue.replace("_", "");
        Pattern extractNumbers = Pattern.compile("([.0-9]+)([hmsd]{1,2})");
        Matcher matcher = extractNumbers.matcher(textValue);

        while (matcher.find()) {
            String num = matcher.group(1);
            String mod = matcher.group(2);
            double factor = getModifier(mod);
            internal = internal.add(BigDecimal.valueOf(factor * Double.parseDouble(num)));
        }
    }

    public TimeValue(double val) {
        internal = BigDecimal.valueOf(val);
    }

    private double getModifier(String mod) {
        switch (mod) {
            case "d":
                return FACTOR_DAY;
            case "h":
                return FACTOR_HOUR;
            case "m":
                return FACTOR_MINUTE;
            case "s":
                return FACTOR_SECONDS;
            case "ms":
                return FACTOR_MILLISECONDS;
            default:
                return 0;
        }
    }

    public long getMilliseconds() {
        return internal.longValue();
    }

    public long getSeconds() {
        return 0;
    }

    public long getMinutes() {
        return 0;
    }

    public long getHours() {
        return 0;
    }

    public long getDays() {
        return 0;
    }
}
