package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.view.spec.table.cells.HybridCellController;
import javafx.beans.property.IntegerProperty;
import javafx.beans.value.ChangeListener;
import javafx.collections.ObservableList;

public class TableColumnController {
    private IntegerProperty width;
    private ObservableList<Type> types;
    private ObservableList<String> typeNames;
    private IOVariable ioVar;
    private ObservableList<HybridCellController> cells;
    /**
     * Gets called if an other type was selected.
     */
    private ChangeListener<String> selectedType;

    public TableColumnController(ObservableList<Type> types, IOVariable ioVar) {
    }

    public IntegerProperty getWidthProperty() {
        return null;
    }

    public int getWidth() {
        return 0;
    }

    public ObservableList<HybridCellController> getCells() {
        return null;
    }
}
