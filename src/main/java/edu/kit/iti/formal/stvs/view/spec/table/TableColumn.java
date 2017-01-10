package edu.kit.iti.formal.stvs.view.spec.table;

import javafx.beans.property.BooleanProperty;
import javafx.scene.layout.Pane;

public class TableColumn extends Pane {
    private BooleanProperty editableProperty;

    public BooleanProperty getEditableProperty() {
        return editableProperty;
    }

    public void setEditable(boolean b) {
    }

    public boolean getEditable() {
        return editableProperty.get();
    }
}
