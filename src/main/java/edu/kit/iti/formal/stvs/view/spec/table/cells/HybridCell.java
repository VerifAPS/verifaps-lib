package edu.kit.iti.formal.stvs.view.spec.table.cells;

import javafx.beans.property.BooleanProperty;

public class HybridCell extends TableCell {
    private BooleanProperty editableProperty;

    public BooleanProperty getEditableProperty() {
        return null;
    }

    public void setEditable(boolean b) {
    }

    public boolean getEditable() {
        return false;
    }
}
