package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.view.spec.table.cells.HybridCellController;
import javafx.beans.property.IntegerProperty;
import javafx.collections.ObservableList;

public class DurationsColumnController {
    private IntegerProperty width;
    private ObservableList<HybridCellController> cells;

    public IntegerProperty getWidthProperty() {
        return width;
    }

    public int getWidth() {
        return width.get();
    }

    public DurationsColumnController() {
    }

    public ObservableList<HybridCellController> getCells() {
        return cells;
    }
}
