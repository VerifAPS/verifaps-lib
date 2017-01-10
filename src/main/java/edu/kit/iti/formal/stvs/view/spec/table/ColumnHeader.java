package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.beans.property.BooleanProperty;
import javafx.scene.layout.Pane;

public class ColumnHeader extends Pane {
    private BooleanProperty editableProperty;
    private String VariableName;
    private Type VariableType;

    public void setVariableName(String name) {
    }

    public void setVariableType(Type type) {
    }

    public BooleanProperty getEditableProperty() {
        return editableProperty;
    }

    public void setEditable(boolean b) {
    }

    public boolean getEditable() {
        return editableProperty.get();
    }
}
