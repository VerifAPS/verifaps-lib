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
import edu.kit.iti.formal.automation.testtables.model.*;
import edu.kit.iti.formal.automation.testtables.schema.Variable;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.ParseException;

import javax.xml.bind.JAXBException;
import java.util.List;
import java.util.Objects;
import java.util.Stack;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (01.02.18)
 */
public class PrintTable {
    public static Stack<Tuple<Duration, Integer>> durations = new Stack<>();

    public static void main(String[] args) throws ParseException, JAXBException {
        CommandLine cli = parse(args);
        for (String s : cli.getArgList()) {
            print(s);
        }
    }

    private static void print(String s) throws JAXBException {
        GeneralizedTestTable table = Facade.readTable(s);
        List<Variable> input = table.getIoVariables().values().stream()
                .filter(v -> Objects.equals(v.getIo(), "input")).collect(Collectors.toList());
        List<Variable> output = table.getIoVariables().values().stream()
                .filter(v -> Objects.equals(v.getIo(), "output")).collect(Collectors.toList());

        int depth = table.getRegion().depth();
        String format = Strings.repeat("c", 1 + depth + table.getIoVariables().size());
        System.out.format("\\begin{tabular}{%s}%n", format);

        System.out.printf("\\# & \\multicolumn{%d}{c}{Input} & " +
                        "\\multicolumn{%d}{c}{Output} & \\coltime \\\\",
                input.size(), output.size());
        System.out.printf("  & %s &%s \\\\",
                input.stream().map(Variable::getName).reduce((a, b) -> a + " & " + b).orElse(""),
                output.stream().map(Variable::getName).reduce((a, b) -> a + " & " + b).orElse(""));

        printRegionLatex(0, table.getRegion());

        System.out.format("\\end{tabular}%n");
    }

    private static int printRegionLatex(int start, Region region) {
        if (region.getDuration() != null) {
            durations.push(Tuple.make(region.getDuration(), region.count()));
        }

        for (TableNode s : region.getChildren()) {
            if (s instanceof Region) {
                start = printRegionLatex(start, (Region) s);
            } else {
                printState(start, (State) s);
                start++;
            }
        }
        return start;
    }

    private static void printState(int start, State s) {
        System.out.printf("%d &", start);
        for (SMVExpr input : s.getInputExpr()) {
            System.out.printf(input.toString() + " & ");
        }
        for (SMVExpr output : s.getOutputExpr()) {
            System.out.printf(output.toString() + " & ");
        }
        System.out.printf(s.getDuration().toString());

        while (!durations.empty()) {
            Tuple<Duration, Integer> d = durations.pop();
            System.out.printf("\\multirow{%d}{%s} &", d.b, d.a);
        }
        System.out.printf("\\\\%n");
    }

    public static CommandLine parse(String[] args) throws ParseException {
        CommandLineParser clp = new DefaultParser();
        org.apache.commons.cli.Options options = new org.apache.commons.cli.Options();
        options.addOption("-f", "format", true, "output format");
        return clp.parse(options, args, true);
    }
}
