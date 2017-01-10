package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.SpecificationTable;
import edu.kit.iti.formal.stvs.model.table.concrete.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.constraint.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.constraint.ConstraintDuration;
import edu.kit.iti.formal.stvs.model.table.hybrid.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.spec.table.rowActions.RowEvent;
import javafx.collections.ObservableList;
import javafx.collections.ObservableMap;
import javafx.collections.ObservableSet;

import java.util.Optional;

public class TablePaneController implements Controller {
    private HybridSpecification spec;
    private ObservableSet<String> definedVars;
    private DurationsColumnController durationColumn;
    private TablePane table;

    /**
     * Listens on changed rows in Specification and adds cells or remove cells in durationColumn
     */
    private void onRowChange(SpecificationTable.RowChangeInfo<ConstraintCell, ConstraintDuration> change){
    }

    /**
     * Listens on changed problem list in Specification and modifies cells in durationColumn
     */
    private void onProblemsChanged(SpecificationTable.RowChangeInfo<ConstraintCell, ConstraintDuration> change){
    }

    /**
     * Listens on changed concrete specification and updates duration cells
     */
    private void onConcreteSpecificationChanged(Optional<ConcreteSpecification> concreteSpecificationOptional){

    }

    private void onAddRowClicked(RowEvent event){

    }
    private void onRemoveRowClicked(RowEvent event){

    }
    private void onCommentRowClicked(RowEvent event){

    }


    public TablePaneController(HybridSpecification spec, ObservableSet<String> definedVars, ObservableList<Type> types, ObservableList<IOVariable> ioVars) {
    }

    public void addIOVariable(IOVariable ioVar) {
    }

    public TablePane getView() {
        return table;
    }
}
