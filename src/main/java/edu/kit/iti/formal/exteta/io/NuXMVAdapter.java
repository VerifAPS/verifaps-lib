package edu.kit.iti.formal.exteta.io;


import edu.kit.iti.formal.smv.ast.SMVModule;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

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
    private SMVModule[] modules;

    public NuXMVAdapter(File table, SMVModule... modules) {
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
            for (SMVModule m :
                    modules) {
                fw.write(m.toString());
                fw.write("\n");
            }
        }
    }

    public boolean isVerified() {
        return process.isVerified();
    }
}
