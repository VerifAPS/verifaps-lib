package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.Value;

import java.util.List;
import java.util.function.Consumer;

/**
 * Created by csicar on 10.01.17.
 */
public class FreeVariable {
    private List<Consumer<FreeVariable>> listeners;

    private String name;
    private Type type;
    private Value defaultValue;

    /**
     * FreeVariable
     * if no default value is given, a default value will be generated
     * @param name
     * @param type
     */
    public FreeVariable(String name, Type type) {
        this.name = name;
        this.type = type;
    }

    public FreeVariable(String name, Type type, Value defaultValue) {
        this.name = name;
        this.type = type;
        this.defaultValue = defaultValue;
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

    public Value getDefaultValue() {
        return defaultValue;
    }

    public void setDefaultValue(Value defaultValue) {
        this.defaultValue = defaultValue;
    }
}
