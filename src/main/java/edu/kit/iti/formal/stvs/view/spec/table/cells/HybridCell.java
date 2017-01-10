package edu.kit.iti.formal.stvs.view.spec.table.cells;

import javafx.beans.property.BooleanProperty;
import javafx.scene.layout.VBox;

public class HybridCell extends TableCell {
    private ValueCell valueCell;
    private VBox counterExampleContainer;
    private BooleanProperty editableProperty;

    public BooleanProperty getEditableProperty() {
        return null;
    }

    public void setEditable(boolean b) {
    }

    public boolean getEditable() {
        return false;
    }

    public VBox getCounterExampleContainer() {
        return counterExampleContainer;
    }

    public ValueCell getValueCell() {
        return valueCell;
    }
}
