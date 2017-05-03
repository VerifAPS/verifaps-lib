package edu.kit.iti.formal.automation.testtables.model;

/**
 * @author Alexander Weigl
 * @version 1 (03.05.17)
 */
public enum VerificationTechnique {
    IC3("read_model", "flatten_hierarchy", "show_vars", "encode_variables",
            "build_boolean_model", "check_invar_ic3", "quit"),

    LTL("read_model", "flatten_hierarchy", "show_vars", "encode_variables",
            "build_model", "check_ltlspec", "quit"),

    INVAR("read_model", "flatten_hierarchy", "show_vars", "encode_variables",
            "build_model", "check_invar", "quit"),

    BMC("read_model", "flatten_hierarchy", "show_vars", "encode_variables",
            "build_boolean_model", "check_invar_bmc -a een-sorrensen", "quit");

    private final String[] commands;

    VerificationTechnique(String... commands) {
        this.commands = commands;
    }

    public String[] getCommands() {
        return commands;
    }
}
