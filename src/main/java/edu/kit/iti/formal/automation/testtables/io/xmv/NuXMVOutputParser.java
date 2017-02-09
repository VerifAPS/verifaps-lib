package edu.kit.iti.formal.automation.testtables.io.xmv;

/*-
 * #%L
 * geteta
 * %%
 * Copyright (C) 2016 - 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.testtables.io.Report;
import edu.kit.iti.formal.automation.testtables.report.Assignment;
import edu.kit.iti.formal.automation.testtables.report.Counterexample;
import org.apache.commons.io.FileUtils;

import java.io.File;
import java.io.IOException;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

public class NuXMVOutputParser {
    public static final Pattern SKIP_MARKER = Pattern.compile("Trace Type: Counterexample");
    public static final Pattern SPLIT_MARKER = Pattern.compile("-> State: (\\d+).(\\d+) <-");
    public static final Pattern INPUT_MARKER = Pattern.compile("-> Input: (\\d+).(\\d+) <-");
    public static final Pattern NEWLINE = Pattern.compile("\n");
    static final Pattern ASSIGNMENT_SEPERATOR = Pattern.compile("(.*)\\s*=\\s*(.*)");

    boolean ceFound = false;
    Counterexample ce;
    boolean invariantHolds;
    boolean errorFound;
    private Stream<String> inputLines;
    private Counterexample.Step currentStep;
    private List<Assignment> current;

    public NuXMVOutputParser(Stream<String> input) {
        inputLines = input;
    }

    public NuXMVOutputParser(File input) throws IOException {
        this(FileUtils.readFileToString(input, "utf-8"));
    }

    public NuXMVOutputParser(String content) {
        this(NEWLINE.splitAsStream(content));
    }

    public Counterexample run() {
        ce = new Counterexample();
        currentStep = new Counterexample.Step();
        current = currentStep.getState();
        //ce.getStep().add(currentStep);

        inputLines.map(String::trim)
                .forEach(this::handle);

        if (ceFound) {
            Report.setErrorLevel("not-verified");
            Report.setCounterExample(ce);
        } else if (invariantHolds)
            Report.setErrorLevel("verified");
        else if (errorFound)
            Report.setErrorLevel("nuxmv-error");
        else
            Report.setErrorLevel("unknown");

        return ce;
    }

    private void handle(String line) {
        if (line.contains("error")
                || line.contains("TYPE ERROR")
                || line.contains("undefined")) {
            Report.fatal("NUXMV error: %s", line);
            errorFound = true;
        } else {
            if (ceFound) {

                if (INPUT_MARKER.matcher(line).matches()) {
                    current = currentStep.getInput();
                    return;
                }

                Matcher m = SPLIT_MARKER.matcher(line);
                if (m.matches()) {
                    int step = Integer.parseInt(m.group(2));
                    currentStep = new Counterexample.Step();
                    ce.getStep().add(currentStep);
                    current = currentStep.getState();
                    return;
                }

                assignment(line);
            } else {
                ceFound = SKIP_MARKER.matcher(line).matches();
                invariantHolds = invariantHolds || line.contains("is true");
            }
        }

    }

    private void assignment(String line) {
        Matcher m = ASSIGNMENT_SEPERATOR.matcher(line);
        if (m.matches()) {
            Assignment a = new Assignment();
            a.setName(m.group(1).trim());
            a.setValue(m.group(2).trim());
            current.add(a);
        }
    }
}
