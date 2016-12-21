package edu.kit.iti.formal.automation;

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

import java.io.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by weigl on 14.11.16.
 */
public class TestUtils {


    public static Iterable<Object[]> loadLines(String filename) throws IOException {
        List<Object[]> validExpression = new ArrayList<>(4096);
        InputStream ve = TestUtils.class.getResourceAsStream(filename);

        if (ve == null) {
            System.err.println("Could not find: " + filename);
            return validExpression;
        }

        BufferedReader stream = new BufferedReader(new InputStreamReader(ve));
        String tmp = "";
        while ((tmp = stream.readLine()) != null) {
            if (tmp.startsWith("#"))
                continue;
            validExpression.add(new Object[]{tmp});
        }

        System.out.println("Found: " + filename + " with " + validExpression.size() + " lines!");

        return validExpression;
    }

    public static Collection<Object[]> asParameters(String[] cases) {
        return Arrays.stream(cases)
                .map(s -> new Object[]{s})
                .collect(Collectors.toList());
    }
}
