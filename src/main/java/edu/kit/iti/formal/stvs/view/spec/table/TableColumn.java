package edu.kit.iti.formal.stvs.view.spec.table;

import javafx.beans.property.BooleanProperty;
import javafx.collections.ObservableList;
import javafx.scene.Node;
import javafx.scene.layout.VBox;

public class TableColumn extends VBox{
    private BooleanProperty editableProperty;

    public BooleanProperty getEditableProperty() {
        return editableProperty;
    }

    public void setEditable(boolean b) {
    }

    public boolean getEditable() {
        return editableProperty.get();
    }

    @Override
    public ObservableList<Node> getChildren() {
        return super.getChildren();
    }
}
