package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.view.spec.table.cells.MultiCellController;
import javafx.beans.property.IntegerProperty;
import javafx.collections.ObservableList;

public class DurationsColumnController {
    private IntegerProperty width;
    private ObservableList<MultiCellController> cells;

    public IntegerProperty getWidthProperty() {
        return width;
    }

    public int getWidth() {
        return width.get();
    }

    public DurationsColumnController() {
    }

    public ObservableList<MultiCellController> getCells() {
        return cells;
    }
}
