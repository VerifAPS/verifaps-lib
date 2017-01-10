package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.code.SourcecodeToken;
import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.view.spec.table.cells.MultiCellController;
import javafx.beans.property.IntegerProperty;
import javafx.collections.ObservableList;

public class TableColumnController {
    private IntegerProperty width;
    private ObservableList<SourcecodeToken.Type> types;
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
