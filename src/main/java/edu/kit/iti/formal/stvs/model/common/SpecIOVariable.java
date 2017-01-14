package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;

/**
 * Created by csicar on 11.01.17.
 */
public class SpecIOVariable extends IOVariable {
    private String name;
    private Type type;
    private VariableCategory category;

    public void setCategory(VariableCategory category) {

    }

    public void setName(String name) {

    }

    public void setType(Type type) {

    }

    @Override
    public VariableCategory getCategory() {
        return null;
    }

    @Override
    public String getName() {
        return null;
    }

    @Override
    public Type getType() {
        return null;
    }
}
