package edu.kit.iti.formal.stvs.view.spec.table.cells;

import javafx.beans.property.ReadOnlyBooleanProperty;

public abstract class TableCell {
    private ReadOnlyBooleanProperty editableProperty;

    public ReadOnlyBooleanProperty getEditableProperty() {
        return null;
    }

    public boolean getEditable() {
        return false;
    }
}
