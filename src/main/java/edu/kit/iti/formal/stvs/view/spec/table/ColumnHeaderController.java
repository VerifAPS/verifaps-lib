package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.beans.property.StringProperty;
import javafx.collections.ObservableList;

public class ColumnHeaderController {
    private StringProperty selectedType;
    private IOVariable ioVar;
    private ObservableList<Type> types;

    public ColumnHeaderController(ObservableList<Type> types, IOVariable ioVar) {
    }
}
