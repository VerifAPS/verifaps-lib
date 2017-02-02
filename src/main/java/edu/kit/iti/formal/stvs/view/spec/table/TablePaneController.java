package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.SpecificationTable;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.spec.table.rowactions.RowEvent;

import java.util.Optional;

public class TablePaneController implements Controller {
  private HybridSpecification spec;
  private DurationsColumnController durationColumn;
  private TablePane table;
  private Selection selection;
  private TableInputController inputTableController;
  private GlobalConfig globalConfig;

  private void onSelectionChange(Selection selection) {

  }

  /**
   * Listens on changed rows in Specification and adds cells or remove cells in durationColumn
   */
  //private void onRowChange(SpecificationTable.RowChangeInfo<ConstraintCell> change) {
  //}

  /**
   * Listens on changed problem list in Specification and modifies cells in durationColumn
   */
  //private void onProblemsChanged(SpecificationTable.RowChangeInfo<ConstraintCell> change) {
  //}

  /**
   * Listens on changed concrete specification and updates duration cells
   */
  private void onConcreteSpecificationChanged(Optional<ConcreteSpecification> concreteSpecificationOptional) {

  }

  private void onAddRowClicked(RowEvent event) {

  }

  private void onRemoveRowClicked(RowEvent event) {

  }

  private void onCommentRowClicked(RowEvent event) {

  }


  public TablePaneController(HybridSpecification spec, GlobalConfig globalConfig) {
    this.globalConfig = globalConfig;
  }

  public void addIoVariable(CodeIoVariable ioVar) {
  }

  public TablePane getView() {
    return table;
  }
}
