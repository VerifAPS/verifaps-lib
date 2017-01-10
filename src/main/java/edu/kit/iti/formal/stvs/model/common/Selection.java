package edu.kit.iti.formal.stvs.model.common;

import java.util.List;
import java.util.function.Consumer;

/**
 * Created by csicar on 10.01.17.
 */
public class Selection {

    private List<Consumer<Selection>> listener;
    private VariableIdentifier ioVariable;
    private int row;

    public Selection(VariableIdentifier ioVariable, int row) {
        this.ioVariable = ioVariable;
        this.row = row;
    }

    public VariableIdentifier getIoVariable() {
        return VariableIdentifier;
    }

    public int getRow() {
        return row;
    }

    public void setIoVariable(VariableIdentifier ioVariable) {
        this.ioVariable = VariableIdentifier;
    }

    public void setRow(int row) {
        this.row = row;
    }

    public void addListener(Consumer<Selection> listener) {

    }
}
