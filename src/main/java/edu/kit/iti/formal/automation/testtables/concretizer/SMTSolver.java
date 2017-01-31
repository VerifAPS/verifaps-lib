package edu.kit.iti.formal.automation.testtables.concretizer;

/**
 * @author Alexander Weigl
 * @version 1 (22.01.17)
 */
public enum SMTSolver {
    Z3("z3 -smt2"), MATHSAT("msat"), YICES("yices");

    private final String commandLine;

    SMTSolver(String commandLine) {
        this.commandLine = commandLine;
    }

    public String getCommandLine() {
        return commandLine;
    }
}
