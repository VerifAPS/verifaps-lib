package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.hybrid.HybridSpecification;
import edu.kit.iti.formal.stvs.view.spec.table.rowActions.RowEvent;
import javafx.collections.ObservableList;
import javafx.collections.ObservableMap;
import javafx.collections.ObservableSet;
import javafx.event.EventHandler;

public class TablePaneController {
    private EventHandler<RowEvent> addRowHandler;
    private EventHandler<RowEvent> removeRowHandler;
    private EventHandler<RowEvent> commentRowHandler;
    private HybridSpecification spec;
    private ObservableSet<String> definedVars;
    private ObservableList<Type> types;
    private ObservableMap<IOVariable, TableColumnController> columns;
    private DurationsColumnController durationColumn;

    public TablePaneController(HybridSpecification spec, ObservableSet<String> definedVars, ObservableList<Type> types, ObservableList<IOVariable> ioVars) {
    }

    public void addIOVariable(IOVariable ioVar) {
    }
}
