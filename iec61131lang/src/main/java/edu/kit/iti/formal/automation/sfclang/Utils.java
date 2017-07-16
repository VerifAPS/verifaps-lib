package edu.kit.iti.formal.automation.sfclang;

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

import lombok.AllArgsConstructor;
import lombok.ToString;

import java.math.BigInteger;
import java.util.Optional;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * <p>Utils class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class Utils {
    static Pattern PATTERN = Pattern.compile("((?<prefix>\\D\\w*?)#)?((?<radix>\\d+?)#)?(?<value>.*)");

    /**
     * <p>getRandomName.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public static String getRandomName() {
        return "action_" + (int) (Math.random() * 10000);
    }


    public static Splitted split(String s) {
        Matcher t = PATTERN.matcher(s);
        if (t.matches()) {
            Splitted r = new Splitted(t.group("prefix"), t.group("radix"), t.group("value"));
            return r;
        } else {
            throw new IllegalArgumentException("Argument is not well word: expected form " + PATTERN.pattern());
        }
    }

    public static BigInteger getIntegerLiteralValue(String text, boolean sign) {
        Splitted s = split(text);
        return sign ? s.number().negate() : s.number();
    }

    @AllArgsConstructor
    @ToString
    public static class Splitted {
        private String prefix, ordinal, value;

        public Optional<String> prefix() {
            return prefix == null ? Optional.empty() : Optional.of(prefix);
        }

        public Optional<String> radix() {
            return ordinal == null ? Optional.empty() : Optional.of(ordinal);
        }

        public Optional<String> value() {
            return value == null ? Optional.empty() : Optional.of(value);
        }

        public BigInteger number() {
            int r = 10;
            if (ordinal != null) {
                r = Integer.parseInt(ordinal);
            }
            return new BigInteger(value, r);
        }
    }
}
