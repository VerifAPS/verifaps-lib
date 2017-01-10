package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.common.VariableIdentifier;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.constraint.problems.SpecProblem;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.spec.table.cells.HybridCellController;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.IntegerProperty;
import javafx.beans.property.ObjectProperty;
import javafx.beans.value.ChangeListener;
import javafx.collections.ObservableList;

import java.util.List;

public class TableColumnController extends ColumnController {
    private IntegerProperty width;
    private ObservableList<Type> types;
    private ObservableList<String> typeNames;
    private ObservableList<HybridCellController> cells;
    private ObjectProperty<VariableIdentifier> ioVar;
    private ObservableList<SpecProblem> problems;

    public TableColumnController(ObservableList<Type> types, ObservableList<IOVariable> ioVars, ObjectProperty<VariableIdentifier> ioVar, ColumnConfig config) {
        super(config);
    }

    @Override
    public void onProblemsChange(List<SpecProblem> problems){

    }

    @Override
    public IntegerProperty getWidthProperty() {
        return null;
    }

    @Override
    public int getWidth() {
        return 0;
    }

    @Override
    public ObservableList<HybridCellController> getCells() {
        return null;
    }

    @Override
    public TableColumn getView() {
        return null;
    }
}
