package edu.kit.iti.formal.automation.testtables.io.xmv;

/*-
 * #%L
 * geteta
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

import edu.kit.iti.formal.automation.testtables.io.Report;
import edu.kit.iti.formal.automation.testtables.report.Counterexample;
import org.apache.commons.io.IOUtils;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Arrays;

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
            NuXMVOutputParser parser = new NuXMVOutputParser(outputFile);
            Counterexample ce = parser.run();
            verified = parser.invariantHolds;
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

}

//file /home/weigl/work/verifaps/exteta/src/test/resources/success.smv: line 9: at token "": syntax error

