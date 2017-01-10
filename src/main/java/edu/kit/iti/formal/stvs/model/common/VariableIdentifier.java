package edu.kit.iti.formal.stvs.model.common;

/**
 * Created by Philipp on 10.01.2017.
 */
public class VariableIdentifier {

    private final String variableName;
    private final VariableCategory category;

    public VariableIdentifier(String variableName, VariableCategory category) {
        this.variableName = variableName;
        this.category = category;
    }
}
