package edu.kit.iti.formal.stvs.view.spec.table;

import javafx.collections.ObservableList;
import javafx.collections.transformation.SortedList;

import java.util.Map;

public class CategoryTableController {
    private String title;
    private HybridSpecification hybridSpecification;
    private ObservableList<Type> types;
    private Predicate<IOVariable> categoryFilter;
    private ObservableList<IOVariables> ioVars;
    private ObservableList<TableColumnController> columns;
    private Map<TableColumnController, Integer> columnIndices;
    private SortedList<TableColumnController> sortedColumns;

    public CategoryTableController(String title, HybridSpecification hybridSpecification, ObservableList<Type> types, Predicate<IOVariable> categoryFilter, ObservableList<IOVariables> ioVars) {
    }

    public ObservableList<TableColumnController> getColumns() {
    }
}
