package edu.kit.iti.formal.automation.testtables.io;

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


import edu.kit.iti.formal.smv.ast.SMVModule;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public class NuXMVAdapter implements Runnable {
    public static final String[] IC3_COMMANDS = new String[]{"read_model",
            "flatten_hierarchy",
            "show_vars",
            "encode_variables",
            "build_boolean_model",
            "check_invar_ic3",
            "quit"};

    private final NuXMVProcess process;
    private List<SMVModule> modules;

    public NuXMVAdapter(File table, List<SMVModule> modules) {
        this.modules = modules;
        this.process = new NuXMVProcess()
                .commands(IC3_COMMANDS)
                .workingDirectory(
                        new File(table.getParentFile(),
                                table.getName().replace(".xml", "")))
                .output(String.format("log_%d.txt", (int) (Math.random() * 100)))
                .module("modules.smv");
    }

    @Override
    public void run() {
        process.workingDirectory().mkdirs();
        try {
            createModuleFile();
        } catch (IOException e) {
            Report.fatal("Could not create module file %s (%s)",
                    process.moduleFile(), e);
            Report.setErrorLevel("io-error");
            System.exit(1);
        }
        process.run();
    }



    private void createModuleFile() throws IOException {
        try (FileWriter fw = new FileWriter(process.moduleFile())) {
            for (SMVModule m : modules) {
                fw.write(m.toString());
                fw.write("\n");
            }
        }
    }

    public boolean isVerified() {
        return process.isVerified();
    }
}
