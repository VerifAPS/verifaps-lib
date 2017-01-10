package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.collections.ObservableList;
import javafx.collections.transformation.SortedList;

import java.util.Map;

abstract public class CategoryTableController {
    private String title;
    private HybridSpecification spec;
    private ObservableList<Type> types;
    private ObservableList<IOVariable> ioVars;
    private ObservableList<TableColumnController> columns;
    private Map<TableColumnController, Integer> columnIndices;
    private SortedList<TableColumnController> sortedColumns;
    private VariableNamePopupController addIOVariablePopup;
    private TablePaneController parent;

    public CategoryTableController(String title, HybridSpecification spec, ObservableList<Type> types, ObservableList<IOVariable> ioVars, TablePaneController tablePaneController) {
    }

    public ObservableList<TableColumnController> getColumns() {
        return columns;
    }

    abstract public void addIOVariable(String string);
}
