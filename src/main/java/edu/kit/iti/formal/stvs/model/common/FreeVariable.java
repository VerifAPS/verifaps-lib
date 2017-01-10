package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;

import java.util.List;
import java.util.function.Consumer;

/**
 * Created by csicar on 10.01.17.
 */
public class FreeVariable {
    private String name;
    private Type type;
    private List<Consumer<FreeVariable>> listeners;

    public FreeVariable(String name, Type type) {
        this.name = name;
        this.type = type;
    }

    public void addChangeListener(Consumer<FreeVariable> listener) {

    }

    public Type getType() {
        return type;
    }

    public void setType(Type type) {
        this.type = type;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }
}
