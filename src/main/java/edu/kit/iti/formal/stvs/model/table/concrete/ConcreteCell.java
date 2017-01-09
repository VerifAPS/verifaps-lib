package edu.kit.iti.formal.stvs.model.table.concrete;

import edu.kit.iti.formal.stvs.model.expressions.Value;

/**
 * Created by philipp on 10.01.17.
 */
public class ConcreteCell {

    private final Value value;

    public ConcreteCell(Value value) {
        this.value = value;
    }

    public Value getValue() {
        return value;
    }
}
