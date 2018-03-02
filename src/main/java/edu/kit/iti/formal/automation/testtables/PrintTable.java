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

import com.google.common.base.Function;
import com.google.common.base.Strings;
import com.google.common.collect.ImmutableList;
import edu.kit.iti.formal.automation.st.util.Tuple;
import edu.kit.iti.formal.automation.testtables.grammar.CellExpressionParser;
import edu.kit.iti.formal.automation.testtables.io.IOFacade;
import edu.kit.iti.formal.automation.testtables.io.TableReader;
import edu.kit.iti.formal.automation.testtables.model.*;
import edu.kit.iti.formal.automation.testtables.schema.IoVariable;
import edu.kit.iti.formal.automation.testtables.schema.Variable;
import org.antlr.v4.runtime.misc.ParseCancellationException;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.ParseException;
import org.w3c.dom.Element;

import javax.annotation.Nonnull;
import javax.xml.bind.JAXBException;
import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (01.02.18)
 */
public class PrintTable {
    private static final String DONT_CARE = "--";
    private static Stack<Tuple<Duration, Integer>> durations = new Stack<>();
    private static GeneralizedTestTable table;
    private static int currentRow = 0;
    private static List<IoVariable> input;
    private static List<IoVariable> output;
    private static HashMap<String, String> cache = new HashMap<>();
    private static Map<String, String> drawLines = new LinkedHashMap<>();
    private static Counter markCounter = new Counter();
    private static HashMap<String, Integer> lastTikzMarkColumn = new HashMap<>();
    private static ImmutableList<String> specialChars = ImmutableList.of("_", "^", "~", "$", "%", "#", "&", "{", "}");
    private static int totalNumSteps;
    private static HashMap<String, ArrayList<String>> columns = new LinkedHashMap<>();

    public static void main(String[] args) throws ParseException, JAXBException {
        CommandLine cli = parse(args);
        for (String s : cli.getArgList()) {
            print(s);
        }
    }

    private static void print(String s) throws JAXBException {
        table = Facade.readTable(s);
        totalNumSteps = table.getRegion().count();
        fillColumns();

        input = table.getIoVariables().values().stream()
                .filter(v -> Objects.equals(v.getIo(), "input")).collect(Collectors.toList());
        output = table.getIoVariables().values().stream()
                .filter(v -> Objects.equals(v.getIo(), "output")).collect(Collectors.toList());

        int depth = table.getRegion().depth();

        System.out.println("\\documentclass{standalone}");
        System.out.println("\\usepackage{booktabs,array,scalerel,microtype,multirow,tikz,boldline}");
        System.out.println("\\usetikzlibrary{calc,arrows,arrows.meta}");
        System.out.println("\\newcommand\\FALSE{FALSE}\n" +
                "\\newcommand\\TRUE{TRUE}\n" +
                "\\newcommand\\DONTCARE{--}\n" +
                "\\newcommand\\singlecopy[1]{#1}\n");
        System.out.println("\\newcommand\\rowgroupduration[2]{%" +
                "\\newcommand\\rowgroupduration[2]{%\n" +
                "  \\multirow{#1}{*}{\n" +
                "    \\tikz{\n" +
                "      \\draw[Bracket-Bracket] (0,0.5ex) -- +($(0,-#1em) - (0,1.5em)$) node[midway]{#2};\n" +
                "    }\n" +
                "  }\n" +
                "}");
        System.out.println("\\usepackage{wasysym}\n");
        System.out.println("\\newcommand{\\coltime}{\\clock}\n");
        System.out.println("\\newcommand{\\drawrepetition}[2]{\\draw[Circle-Circle] (#1) -- (#2);}\n");
        System.out.println("\\newcommand\\variableheader[1]{#1}");
        System.out.println("\\newcommand\\categoryheader[1]{#1}");
        System.out.println("\\newcommand\\tikzmark[1]{\\tikz[remember picture,overlay] \\coordinate (#1);}\n");

        System.out.println("\\begin{document}\n");

        System.out.format("\\begin{tabular}{c|%s|%s|%s}%n",
                Strings.repeat("c", input.size()),
                Strings.repeat("c", output.size()),
                Strings.repeat("c", depth + 1));

        System.out.printf("\\# & \\multicolumn{%d}{c}{\\categoryheader{Input}} & " +
                        "\\multicolumn{%d}{c}{\\categoryheader{Output}} & \\coltime \\\\%n",
                input.size(), output.size());

        Function<String, String> wrapColumnHeader = (String hdr) -> "\\variableheader{" + hdr + "}";

        System.out.printf("  & %s &%s \\\\%n",
                input.stream().map(Variable::getName)
                        .map(PrintTable::escape)
                        .map(wrapColumnHeader)
                        .reduce((a, b) -> a + " & " + b).orElse(""),
                output.stream().map(Variable::getName)
                        .map(PrintTable::escape)
                        .map(wrapColumnHeader)
                        .reduce((a, b) -> a + " & " + b).orElse(""));

        System.out.println("\\toprule");

        printRegionLatex(table.getRegion().getChildren());

        System.out.format("\\bottomrule\n\\end{tabular}%n");

        System.out.println("\\begin{tikzpicture}[remember picture, overlay]");
        drawLines.forEach((from, to) -> {
            System.out.printf("\\drawrepetition{%s}{%s}%n", from, to);
        });
        System.out.println("\\end{tikzpicture}");
        System.out.println("\\end{document}");
    }

    private static void fillColumns() {
        table.getIoVariables().forEach((k, v) -> {
            columns.put(k, new ArrayList<>());
        });

        //prefill
        table.getRegion().flat()
                .forEach(s -> {
                    s.getEntryForColumn().forEach((k, v) -> {
                        columns.get(k).add(parseAndSafePrint(Strings.nullToEmpty(v)));
                    });
                });

        //simplify
        columns.forEach((k, v) -> {
            if (v.get(0).isEmpty())
                v.set(0, "-");

            for (int i = 0; i < v.size() - 1; ) {
                int j = i + 1;
                // delete any cell contents, that is same as i
                for (; j < v.size() &&
                        (v.get(i).equals(v.get(j)) ||
                                v.get(j).isEmpty())
                        ; j++) {
                    v.set(j, "");
                }

                if (j == i + 2) {//one empty cell
                    v.set(i + 1, "\\singlecopy{" + v.get(i) + "}");
                } else if (j > i + 2) {//more than one empty
                    v.set(i + 1, tikzMark(k));
                    v.set(j - 1, tikzMarkAndDraw(k));
                }
                i = j;
            }
        });
    }

    private static String parseAndSafePrint(String expr) {
        if (expr.isEmpty()) return "";
        CellExpressionParser cep = IOFacade.createParser(expr);
        LatexPrinter latexPrinter = new LatexPrinter();
        try {
            CellExpressionParser.CellContext ctx = cep.cell();
            return ctx.accept(latexPrinter);
        } catch (ParseCancellationException e) {
            System.err.println("Input: '" + expr + "'");
            e.printStackTrace();
            throw e;
        }
    }

    static String escape(String s) {
        for (String sc : specialChars) {
            s = s.replace(sc, '\\' + sc);
        }
        return s;
    }

    private static void printRegionLatex(List<TableNode> region) {
        for (Object o : region) {
            if (o instanceof State) {
                printStep((State) o);
            }
            if (o instanceof Region) {
                System.out.println("\\midrule");
                printRegionLatex((Region) o);
                System.out.println("\\midrule");
            }
        }
    }

    private static void printRegionLatex(Region b) {
        durations.push(Tuple.make(b.getDuration(), b.count()));
        printRegionLatex(b.getChildren());
    }

    /*
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
    */

    private static void printStep(State s) {
        System.out.printf("%2d", currentRow++);
        //List<Element> any = s.getAny().stream().map(Element.class::cast).collect(Collectors.toList());

        input.forEach(v ->
                System.out.printf(" & %15s", columns.get(v.getName()).get(currentRow - 1))
        );

        output.forEach(v ->
                System.out.printf(" & %15s", columns.get(v.getName()).get(currentRow - 1))
        );

        System.out.printf(" & %15s", beautifyDuration(s.getDuration()));
        while (!durations.empty()) {
            Tuple<Duration, Integer> d = durations.pop();
            System.out.printf(" & \\rowgroupduration{%d}{%s}", d.b, beautifyDuration(d.a));
        }
        System.out.printf("\\\\%n");
    }

    private static String beautifyDuration(Duration d) {
        if (d.isDeterministicWait())
            return "\\textsc{dwait}";

        if (d.isOmega())
            return "$\\omega$";

        if (d.isOneStep())
            return "$1$";

        if (d.isUnbounded())
            return String.format("$\\geq%s$", d.getLower());

        return String.format("$[%d,%d]$", d.getLower(), d.getUpper());
    }

    private static String get(List<Element> s, String varName, boolean lastRow) {
        String value = TableReader.get(s, varName);
        String cacheValue = cache.get(varName);
        if (value != null) { //value defined
            cache.put(varName, value); //save into cache
            if (value.equals(cacheValue)) //if variable is the same, to nothing
                return lastRow ? tikzMarkAndDraw(varName) : "";
            return tikzMarkAndDraw(varName) + escape(value); //else return new value.
        }
        if (cacheValue == null) {
            cache.put(varName, "-");
            return DONT_CARE + tikzMark(varName); //first row
        } else {
            return lastRow ? tikzMarkAndDraw(varName) : "";
        }
    }

    private static String tikzMark(String varName) {
        int c = markCounter.getAndIncrement(varName);
        lastTikzMarkColumn.put(varName, c);
        return String.format("\\tikzmark{%s%s}", varName, c);
    }


    private static String tikzMarkAndDraw(String varName) {
        int c = markCounter.getAndIncrement(varName);
        if (lastTikzMarkColumn.containsKey(varName)) {
            int b = lastTikzMarkColumn.get(varName);
            drawLines.put(varName + b, varName + c);
        }
        lastTikzMarkColumn.put(varName, c);
        return String.format("\\tikzmark{%s%s}", varName, c);
    }

    public static CommandLine parse(String[] args) throws ParseException {
        CommandLineParser clp = new DefaultParser();
        org.apache.commons.cli.Options options = new org.apache.commons.cli.Options();
        options.addOption("f", "format", true, "output format");
        return clp.parse(options, args, true);
    }


    public static class Counter {
        private final HashMap<String, Integer> counter = new LinkedHashMap<>();

        public int peek(@Nonnull String s) {
            return counter.computeIfAbsent(s, (a) -> 0);
        }

        public int getAndIncrement(String s) {
            int peek = peek(s);
            counter.put(s, peek + 1);
            return peek;
        }
    }
}
