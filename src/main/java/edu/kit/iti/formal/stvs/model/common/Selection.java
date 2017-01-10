package edu.kit.iti.formal.stvs.model.common;

import java.util.List;
import java.util.Optional;
import java.util.function.Consumer;

/**
 * Created by csicar on 10.01.17.
 */
public class Selection {

    private List<Consumer<Selection>> listener;
    private Optional<VariableIdentifier> variableIdentifier;
    private Optional<Integer> row;

    public Selection(VariableIdentifier variableIdentifier, int row) {
        this.variableIdentifier = Optional.ofNullable(variableIdentifier);
        this.row = Optional.ofNullable(row);
    }

    public Selection() {
        this.variableIdentifier = Optional.empty();
        this.row = Optional.empty();
    }

    public Optional<VariableIdentifier> getVariableIdentifier() {
        return variableIdentifier;
    }

    public Optional<Integer> getRow() {
        return row;
    }

    public void setVariableIdentifier(VariableIdentifier variableIdentifier) {
        this.variableIdentifier = Optional.ofNullable(variableIdentifier);
    }

    public void setRow(int row) {
        this.row = Optional.ofNullable(row);
    }

    public void addListener(Consumer<Selection> listener) {

    }
}
