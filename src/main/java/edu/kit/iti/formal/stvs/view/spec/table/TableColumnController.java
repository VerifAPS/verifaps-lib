package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.view.spec.table.cells.MultiCellController;
import javafx.beans.property.IntegerProperty;
import javafx.collections.ObservableList;

public class TableColumnController {
    private IntegerProperty width;
    private ObservableList<Type> types;
    private IOVariable ioVar;
    private ObservableList<MultiCellController> cells;

    public TableColumnController(ObservableList<Type> types, IOVariable ioVar) {
    }

    public IntegerProperty getWidthProperty() {
        return null;
    }

    public int getWidth() {
        return 0;
    }

    public ObservableList<MultiCellController> getCells() {
        return null;
    }
}
