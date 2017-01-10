package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.common.VariableIdentifier;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.SpecificationTable;
import edu.kit.iti.formal.stvs.model.table.constraint.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.constraint.ConstraintDuration;
import edu.kit.iti.formal.stvs.model.table.constraint.problems.SpecProblem;
import edu.kit.iti.formal.stvs.model.table.hybrid.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.ObservableList;
import javafx.collections.ObservableMap;
import javafx.event.ActionEvent;
import javafx.scene.Node;

import java.util.List;
import java.util.Map;

abstract public class CategoryTableController implements Controller {
    private String title;
    private HybridSpecification spec;
    private ObservableList<Type> types;
    private ObservableList<IOVariable> ioVars;

    private ObservableMap<VariableIdentifier, ColumnController> columns;
    private Map<ColumnController, Integer> columnIndices;
    private ObservableList<ColumnController> sortedColumns;

    /**
     * Gets called if button for new IOVariable is pressed.
     * Creates IOVariableNamePopupController.
     */
    private void onNewIOVariableButton(ActionEvent e) {

    }

    /**
     * Listens on changed rows in Specification model and adds cells, removes cells in columns
     */
    private void onRowChange(SpecificationTable.RowChangeInfo<ConstraintCell, ConstraintDuration> change) {

    }

    /**
     * Listens on changed columns in Specification model and adds columns, removes columns
     */
    protected void onColumnChange(SpecificationTable.ColumnChangeInfo<ConstraintCell> change) {
    }

    private void onSpecProblemsChanged(List<SpecProblem> problems){

    }

    public CategoryTableController(String title, HybridSpecification spec, ObservableList<Type> types, ObservableList<IOVariable> ioVars, TablePaneController tablePaneController) {
    }

    public ObservableList<ColumnController> getColumns() {
        return sortedColumns;
    }

    /**
     * Adds a column of an IOVariable that exists in the code or is newly defined.
     * Automatically adds view listeners for drag detected, mouse moved and drag done to column.
     * Automatically adds model listener to spec.rowsListeners to add remove cells on row change.
     *
     * @param string name of Variable
     */
    abstract public void addIOVariable(String string);

    /**
     * Resorts
     */
    private void updateSort() {

    }

    public Node getView() {
        return null;
    }
}
