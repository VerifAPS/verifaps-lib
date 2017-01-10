package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.StringProperty;
import javafx.collections.ObservableList;
import javafx.scene.Node;

public class ColumnHeaderController implements Controller {
    private StringProperty selectedType;
    private IOVariable ioVar;
    private ObservableList<Type> types;

    public ColumnHeaderController(ObservableList<Type> types, IOVariable ioVar) {
    }

    @Override
    public ColumnHeader getView() {
        return null;
    }
}
