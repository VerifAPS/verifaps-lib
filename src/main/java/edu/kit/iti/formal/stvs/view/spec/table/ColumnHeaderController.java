package edu.kit.iti.formal.stvs.view.spec.table;

import javafx.beans.property.StringProperty;

public class ColumnHeaderController {
    private StringProperty selectedType;
    private IOVariable ioVar;
    private ObservableList<Type> types;

    public ColumnHeaderController(ObservableList<Type> types, IOVariable ioVar) {
    }
}
