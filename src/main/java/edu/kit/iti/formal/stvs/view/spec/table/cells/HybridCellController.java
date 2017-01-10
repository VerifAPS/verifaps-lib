package edu.kit.iti.formal.stvs.view.spec.table.cells;

import edu.kit.iti.formal.stvs.model.table.CellOperationProvider;
import javafx.beans.property.StringProperty;
import javafx.collections.ObservableList;

import java.util.function.Consumer;

public class HybridCellController {
    private StringProperty comment;
    private ObservableList<String> counterexamples;
    private ValueCellController valueCellController;
    private Consumer<String> addUserInputStringListener;

    public ObservableList<String> getCounterexamples() {
        return null;
    }

    public StringProperty getValueProperty() {
        return null;
    }

    public StringProperty getCommentProperty() {
        return null;
    }
    public HybridCellController(CellOperationProvider cell, ObservableList<String> counterexamples){
    }
}
