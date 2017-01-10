package edu.kit.iti.formal.stvs.view.spec.table.cells;

import javafx.beans.property.ReadOnlyBooleanProperty;
import javafx.scene.layout.Pane;

public abstract class TableCell extends Pane {
    private ReadOnlyBooleanProperty editableProperty;

    public ReadOnlyBooleanProperty getEditableProperty() {
        return null;
    }

    public boolean getEditable() {
        return false;
    }
}
