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

import java.time.Duration;
import java.time.format.DateTimeParseException;
import java.util.concurrent.TimeUnit;

@NoArgsConstructor
@AllArgsConstructor
@Data
public class TimeValue {
    private long milliseconds;

    public TimeValue(String textValue) {
        try {
            milliseconds = Duration.parse("PT" + textValue).toMillis();
        } catch (DateTimeParseException e) {
            System.err.println(textValue);
            e.printStackTrace();
        }
    }

    public long getDays() {
        return TimeUnit.MILLISECONDS.toDays(milliseconds);
    }

    public long getHours() {
        return TimeUnit.MILLISECONDS.toHours(milliseconds);
    }

    public long getMinutes() {
        return TimeUnit.MILLISECONDS.toMinutes(milliseconds);
    }

    public long getSeconds() {
        return TimeUnit.MILLISECONDS.toSeconds(milliseconds);
    }
}
