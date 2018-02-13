/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
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
 */
package edu.kit.iti.formal.automation.testtables;

/*-
 * #%L
 * geteta
 * %%
 * Copyright (C) 2017 - 2018 Alexander Weigl
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

import com.google.common.base.Strings;
import edu.kit.iti.formal.automation.st.util.Tuple;
import edu.kit.iti.formal.automation.testtables.io.TableReader;
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.schema.*;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.ParseException;
import org.w3c.dom.Element;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;
import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.Objects;
import java.util.Stack;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (01.02.18)
 */
public class PrintTable {
    public static Stack<Tuple<String, Integer>> durations = new Stack<>();
    public static GeneralizedTestTable table;
    public static TestTable xml;
    private static int currentRow = 0;
    private static List<IoVariable> input;
    private static List<IoVariable> output;
    private static HashMap<String, String> cache = new HashMap<>();

    public static void main(String[] args) throws ParseException, JAXBException {
        CommandLine cli = parse(args);
        for (String s : cli.getArgList()) {
            print(s);
        }
    }

    private static void print(String s) throws JAXBException {
        @SuppressWarnings("restriction") JAXBContext jc = JAXBContext
                .newInstance(ObjectFactory.class);
        Unmarshaller jaxbUnmarshaller = jc.createUnmarshaller();
        JAXBElement<?> root = (JAXBElement<?>) jaxbUnmarshaller
                .unmarshal(new File(s));
        xml = (TestTable) root.getValue();
        table = Facade.readTable(s);

        input = table.getIoVariables().values().stream()
                .filter(v -> Objects.equals(v.getIo(), "input")).collect(Collectors.toList());
        output = table.getIoVariables().values().stream()
                .filter(v -> Objects.equals(v.getIo(), "output")).collect(Collectors.toList());

        int depth = table.getRegion().depth();
        System.out.format("\\begin{tabular}{c|%s|%s|%s}%n",
                Strings.repeat("c", input.size()),
                Strings.repeat("c", output.size()),
                Strings.repeat("c", depth + 1));

        System.out.printf("\\# & \\multicolumn{%d}{c}{Input} & " +
                        "\\multicolumn{%d}{c}{Output} & \\coltime \\\\%n",
                input.size(), output.size());
        System.out.printf("  & %s &%s \\\\%n",
                input.stream().map(Variable::getName).reduce((a, b) -> a + " & " + b).orElse(""),
                output.stream().map(Variable::getName).reduce((a, b) -> a + " & " + b).orElse(""));

        printRegionLatex(xml.getSteps().getBlockOrStep());

        System.out.format("\\bottomrule\n\\end{tabular}%n");
    }

    private static void printRegionLatex(List<Object> region) {
        for (Object o : region) {
            if (o instanceof Step) {
                printStep((Step) o);
            }
            if (o instanceof Block) {
                System.out.println("\\midrule");
                printRegionLatex((Block) o);
                System.out.println("\\midrule");
            }
        }
    }

    private static void printRegionLatex(Block b) {
        durations.push(Tuple.make(b.getDuration(), countSteps(b)));
        printRegionLatex(b.getStepOrBlock());
    }

    private static int countSteps(Block b) {
        int count = 0;
        for (Object o : b.getStepOrBlock()) {
            if (o instanceof Step) {
                count += 1;
            }
            if (o instanceof Block) {
                count += countSteps((Block) o);
            }
        }
        return count;
    }

    private static void printStep(Step s) {
        System.out.printf("%2d", currentRow++);
        List<Element> any = s.getAny().stream().map(Element.class::cast).collect(Collectors.toList());
        input.forEach(v ->
                System.out.printf(" & %15s", get(any, v.getName()))
        );

        output.forEach(v ->
                System.out.printf(" & %15s", get(any, v.getName()))
        );

        System.out.printf(" & %15s", s.getDuration());
        while (!durations.empty()) {
            Tuple<String, Integer> d = durations.pop();
            System.out.printf(" & \\multirow{%d}{*}{%s}", d.b, beautifyDuration(d.a));
        }
        System.out.printf("\\\\%n");
    }

    private static String beautifyDuration(String d) {
        switch (d) {
            case "omega":
                return "$\\omega$";
            case "wait":
                return "\\textsc{wait}";
            default:
                return String.format("$%s$", d);
        }
    }

    private static String get(List<Element> s, String varName) {
        String value = TableReader.get(s, varName);
        String cacheValue = cache.get(varName);
        if (value != null) {
            cache.put(varName, value);
            if (value.equals(cacheValue))
                return "";
            return value;
        }
        if (cacheValue == null) {
            cache.put(varName, "-");
            return "-";
        } else {
            return "";
        }
    }

    public static CommandLine parse(String[] args) throws ParseException {
        CommandLineParser clp = new DefaultParser();
        org.apache.commons.cli.Options options = new org.apache.commons.cli.Options();
        options.addOption("f", "format", true, "output format");
        return clp.parse(options, args, true);
    }
}
