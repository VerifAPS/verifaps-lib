package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.view.spec.table.rowActions.RowEvent;
import javafx.collections.ObservableSet;

public class TablePaneController {
    private EventHandler<RowEvent> addRowHandler;
    private EventHandler<RowEvent> removeRowHandler;
    private EventHandler<RowEvent> commentRowHandler;
    private ExpressionParser parser;
    private Specification spec;
    private ObservableSet<String> definedVars;
    private ObservableList<Type> types;
    private ObservableMap<IOVariable, TableColumnController> columns;
    private DurationsColumnController durationColumn;

    public TablePaneController(HybridSpecification hybridSpecification, ObservableSet<String> definedVars, ObservableList<Type> types, ObservableList<IOVariables> ioVars) {
    }
}
