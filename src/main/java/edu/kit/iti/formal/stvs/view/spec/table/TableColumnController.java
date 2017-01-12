package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIOVariable;
import edu.kit.iti.formal.stvs.model.common.VariableIdentifier;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import edu.kit.iti.formal.stvs.view.spec.table.cells.HybridCellController;
import javafx.beans.property.IntegerProperty;
import javafx.beans.property.ObjectProperty;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;

import java.util.List;

public class TableColumnController extends ColumnController {
    private IntegerProperty width;
    private ObservableList<Type> types;
    private ObservableList<String> typeNames;
    private ObservableList<HybridCellController> cells;
    private ObjectProperty<VariableIdentifier> ioVar;
    private ObservableList<SpecProblem> problems;
    private TableColumn tableColumn;
    private GlobalConfig globalConfig;
    private ContextMenu contextMenu;

    public TableColumnController(ObservableList<Type> types, ObservableList<CodeIOVariable> ioVars, ObjectProperty<VariableIdentifier> ioVar, ColumnConfig config, GlobalConfig globalConfig) {
        super(config);
        this.globalConfig = globalConfig;
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
        return tableColumn;
    }
}
