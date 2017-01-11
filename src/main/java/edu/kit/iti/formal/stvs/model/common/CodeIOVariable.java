package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;

/**
 * Created by philipp on 09.01.17.
 */
public class CodeIOVariable extends IOVariable {

    private VariableCategory category;
    private Type type;
    private String name;

    public CodeIOVariable(VariableCategory category, Type type, String name) {
        this.category = category;
        this.type = type;
        this.name = name;
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
