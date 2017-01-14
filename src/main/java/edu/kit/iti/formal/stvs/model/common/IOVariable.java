package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;

/**
 * Created by csicar on 11.01.17.
 */
public abstract class IOVariable {


    public abstract VariableCategory getCategory();
    public abstract String getName();
    public abstract Type getType();

    public boolean matches(IOVariable other) {
        return false;
    }
}
