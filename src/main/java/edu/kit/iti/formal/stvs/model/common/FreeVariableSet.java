package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.config.ColumnConfig;

import java.util.List;
import java.util.Set;
import java.util.function.Consumer;

/**
 * Created by csicar on 10.01.17.
 */
public class FreeVariableSet {
    private List<FreeVariable> variableSet;
    private List<Consumer<FreeVariableSet>> listeners;

    public FreeVariableSet(List<FreeVariable> variableSet) {
        this.variableSet = variableSet;
    }

    public void addChangeListener(Consumer<FreeVariableSet> listener) {

    }

    public List<FreeVariable> getVariableSet() {
        return variableSet;
    }

    public void setVariableSet(List<FreeVariable> variableSet) {
        this.variableSet = variableSet;
    }
}
