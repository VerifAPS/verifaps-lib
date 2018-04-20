package edu.kit.iti.formal.smv.parser;

/*-
 * #%L
 * ProofScriptParser
 * %%
 * Copyright (C) 2017 Application-oriented Formal Verification
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


import edu.kit.iti.formal.smv.ast.SMVExpr;
import org.antlr.v4.runtime.CharStreams;

import java.io.*;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (27.04.17)
 */
public class TestHelper {
    public static String getFile(String path) {
        return getFile(TestHelper.class, path);
    }

    public static String getFile(Class<?> aClass, String path) {
        return aClass.getResource(path).toExternalForm().substring(5);
    }

    public static Iterable<Object[]> getResourcesAsParameters(String folder) {
        File[] files = getResources(folder);
        return Arrays.stream(files).map(f -> new Object[]{f}).collect(Collectors.toList());
    }

    public static final File[] getResources(String folder) {
        URL f = TestHelper.class.getClassLoader().getResource(folder);
        if (f == null) {
            System.err.format("Could not find %s%n", folder);
            return new File[0];
        }
        File file = new File(f.getFile());
        return file.listFiles();
    }

    public static Iterable<Object[]> loadLines(String filename, int expectedArgs) throws IOException {
        List<Object[]> validExpression = new ArrayList<>(4096);
        InputStream ve = TestHelper.class.getResourceAsStream(filename);

        if (ve == null) {
            System.err.println("Could not find: " + filename);
            return validExpression;
        }

        BufferedReader stream = new BufferedReader(new InputStreamReader(ve));
        String tmp = "";
        while ((tmp = stream.readLine()) != null) {
            if (tmp.startsWith("#") || tmp.isEmpty())
                continue;
            String[] split = tmp.split(">>>");
            if (split.length != expectedArgs) {
                System.err.format("Line %s has %d arguments, expected %d. SKIPPED%n",
                        tmp, split.length, expectedArgs);
                continue;
            }
            validExpression.add(split);
        }

        System.out.println("Found: " + filename + " with " + validExpression.size() + " lines!");

        return validExpression;
    }


    public static Collection<Object[]> asParameters(String[] cases) {
        return Arrays.stream(cases).map(s -> new Object[]{s}).collect(Collectors.toList());
    }

    public static SMVParser getParser(String input) {
        return Facade.INSTANCE.getParser(CharStreams.fromString(input));
    }

    public static SMVParser getParser(File f) throws IOException {
        return Facade.INSTANCE.getParser(CharStreams.fromFileName(f.getAbsolutePath()));
    }

    public static SMVExpr toExpr(String s) {
        SMVTransformToAST v = new SMVTransformToAST();
        SMVExpr e = (SMVExpr) getParser(s).expr().accept(v);
        return e;
    }
}
