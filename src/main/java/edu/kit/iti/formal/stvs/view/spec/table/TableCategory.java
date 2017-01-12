package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.view.spec.Lockable;
import javafx.beans.property.BooleanProperty;
import javafx.collections.ObservableList;
import javafx.scene.Node;
import javafx.scene.layout.HBox;

public class TableCategory extends HBox implements Lockable {
    @Override
    public ObservableList<Node> getChildren() {
        return super.getChildren();
    }

    @Override
    public boolean getEditable() {
        return false;
    }

    @Override
    public void setEditable(boolean b) {

    }

    @Override
    public BooleanProperty getEditableProperty() {
        return null;
    }
}
