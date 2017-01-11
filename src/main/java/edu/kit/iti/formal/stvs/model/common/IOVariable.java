package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;

/**
 * Created by philipp on 09.01.17.
 */
public class IOVariable {

    private VariableCategory category;
    private Type type;
    private String name;

    public IOVariable(VariableCategory category, Type type, String name) {
        this.category = category;
        this.type = type;
        this.name = name;
    }

    public VariableCategory getCategory() {
        return category;
    }

    public Type getType() {
        return type;
    }

    public void setType(Type type) {

    }

    public VariableIdentifier toVariableIdentifier() {
        return null;
    }

}
