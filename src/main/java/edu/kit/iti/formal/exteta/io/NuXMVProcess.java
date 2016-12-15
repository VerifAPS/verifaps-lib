package edu.kit.iti.formal.exteta.io;

import edu.kit.iti.formal.exteta.report.*;
import org.apache.commons.io.IOUtils;

import java.io.*;
import java.nio.charset.Charset;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (13.12.16)
 */
public class NuXMVProcess implements Runnable {
    public static final String IC3_XMV = "commands.xmv";
    private String[] commands;
    private String executablePath = System.getenv().getOrDefault("NUXMV", "nuXmv");
    private File moduleFile;
    private File workingDirectory;
    private File outputFile;
    private boolean verified;

    //region builder

    public NuXMVProcess output(String path) {
        return outputFile(new File(workingDirectory, path));
    }

    public NuXMVProcess module(String path) {
        return moduleFile(new File(workingDirectory, path));
    }

    public File outputFile() {
        return outputFile;
    }

    public NuXMVProcess outputFile(File f) {
        outputFile = f;
        return this;
    }

    public String[] commands() {
        return commands;
    }

    public NuXMVProcess commands(String... commands) {
        this.commands = commands;
        return this;
    }

    public String executablePath() {
        return executablePath;
    }

    public NuXMVProcess executablePath(String executablePath) {
        this.executablePath = executablePath;
        return this;
    }

    public File moduleFile() {
        if (moduleFile == null)
            module("source.xmv");
        return moduleFile;
    }

    public NuXMVProcess moduleFile(File moduleFile) {
        this.moduleFile = moduleFile;
        return this;
    }

    public File workingDirectory() {
        return workingDirectory;
    }

    public NuXMVProcess workingDirectory(File workingDirectory) {
        this.workingDirectory = workingDirectory;
        return this;
    }
    //endregion

    @Override
    public void run() {
        workingDirectory.mkdirs();
        String[] commands = new String[]{executablePath, "-int",
                moduleFile().getAbsolutePath()};

        try {
            createIC3CommandFile();
        } catch (IOException e) {
            Report.error("Could not create command file: %s in %s", IC3_XMV, workingDirectory);
            Report.setErrorLevel("io-error"); //TODO more detail in error level?
            return;
        }


        try {
            ProcessBuilder pb = new ProcessBuilder(commands)
                    .directory(workingDirectory)
                    .redirectOutput(outputFile)
                    .redirectInput(new File(workingDirectory, IC3_XMV))
                    .redirectErrorStream(true);

            Report.info("Start '%s'", Arrays.toString(commands));
            Report.info("wd: %s", workingDirectory);
            Report.info("Result in %s", outputFile);

            Process p = pb.start();
            p.waitFor();
            Counterexample ce = NuXMVOutputParser.parseOutput(outputFile);
            verified = ce == null;
        } catch (IOException e) {
            Report.error("Error in running nuxmv: %s", e.getMessage());
            Report.error("Command line are: %s", Arrays.toString(commands));
            Report.setErrorLevel("error"); //TODO more detail in error level?
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }


    private void createIC3CommandFile() throws IOException {
        workingDirectory().mkdirs();
        File f = new File(workingDirectory, IC3_XMV);
        try (FileWriter fw = new FileWriter(f)) {
            IOUtils.writeLines(Arrays.asList(commands), "\n", fw);
        }
    }


    public boolean isVerified() {
        return verified;
    }

    static class NuXMVOutputParser {
        static final String SKIP_MARKER = "Counterexample";
        static final String START_MARKER = "-> State: 1.1 <-";
        static final Pattern STATE_SEPERATOR = Pattern.compile("-> Input: .* <-");
        static final String ASSIGNMENT_SEPERATOR = "=";
        static final Pattern INPUT_STATE_SEPERATOR = Pattern.compile("-> .* <-");
        public static final Pattern NEWLINE = Pattern.compile("\n");

        private static Counterexample parseOutput(File input) throws IOException {
            Counterexample ce = new Counterexample();
            try (BufferedReader fr = new BufferedReader(new FileReader(input))) {
                String content = IOUtils.toString(fr);
                int posCe = content.indexOf(SKIP_MARKER);
                if (posCe >= 0) {
                    content = content.substring(content.indexOf(START_MARKER));
                    String[] states = STATE_SEPERATOR.split(content);
                    List<Counterexample.Step> l = Arrays.stream(states)
                            .map(NuXMVOutputParser::parseState)
                            .collect(Collectors.toList());
                    ce.getStep().addAll(l);
                    Report.setErrorLevel("not-verified");
                    Report.setCounterExample(ce);
                } else {
                    if (content.contains("is true")) {
                        Report.setErrorLevel("verified");
                        return null;
                    } else {
                        Report.setErrorLevel("nuxmv-error");
                        handleErrors(content);
                        return ce;
                    }
                }
            }
            return ce;
        }

        private static void handleErrors(String content) {
            NEWLINE.splitAsStream(content).forEach(
                    line ->
                    {
                        if (line.contains("error")
                                || line.contains("TYPE ERROR")
                                || line.contains("undefined"))
                            Report.fatal("NUXVM error: %s", line);
                    });
        }

        private static Counterexample.Step parseState(String state) {
            Function<String, Assignment> parseLine = (String line) -> {
                if (line.trim().isEmpty())
                    return null;
                String[] s = line.split(ASSIGNMENT_SEPERATOR);
                if (s.length != 2)
                    return null;
                Assignment a = new Assignment();
                a.setName(s[0].trim());
                a.setValue(s[1].trim());
                return a;
            };

            Counterexample.Step step = new Counterexample.Step();

            // split into input/output

            String[] io = INPUT_STATE_SEPERATOR.split(state);

            NEWLINE.splitAsStream(io[0])
                    .map(parseLine)
                    .filter(Objects::nonNull)
                    .forEachOrdered(step.getInput()::add);
            NEWLINE.splitAsStream(io[1])
                    .map(parseLine)
                    .filter(Objects::nonNull)
                    .forEachOrdered(step.getState()::add);

            return step;
        }

    }
}

//file /home/weigl/work/verifaps/exteta/src/test/resources/success.smv: line 9: at token "": syntax error

