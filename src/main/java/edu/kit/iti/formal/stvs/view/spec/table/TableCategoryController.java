package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationTable;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.ObservableMap;
import javafx.event.ActionEvent;
import javafx.scene.control.ContextMenu;

import java.util.List;
import java.util.Map;
import java.util.Optional;

abstract public class TableCategoryController implements Controller {
  private String title;
  private HybridSpecification spec;
  private TableCategory tableCategory;
  private ContextMenu contextMenu;

  private ObservableMap<String, ColumnController> columns;
  private Map<ColumnController, Integer> columnIndices;


  /**
   * Gets called if button for new CodeIoVariable is pressed.
   * Creates IoVariableNamePopupController.
   */
  private void onNewIoVariableButton(ActionEvent e) {

  }

  /**
   * Listens on changed rows in Specification model and adds cells, removes cells in columns
   */
  private void onRowChange(SpecificationTable.RowChangeInfo<ConstraintCell> change) {

  }

  /**
   * Listens on changed columns in Specification model and adds columns, removes columns
   */
  protected void onColumnChange(SpecificationTable.ColumnChangeInfo<ConstraintCell> change) {
  }

  private void onSpecProblemsChanged(List<SpecProblem> problems) {

  }

  public TableCategoryController(String title, HybridSpecification spec, TablePaneController tablePaneController) {
  }


  /**
   * Adds a column of an CodeIoVariable that exists in the code or is newly defined.
   * Automatically adds view listeners for drag detected, mouse moved and drag done to column.
   * Automatically adds model listener to spec.rowsListeners to add remove cells on row change.
   *
   * @param string name of Variable
   */
  abstract public void addIoVariable(String string);

  /**
   * Resorts columns
   */
  private void updateSort() {

  }

  /**
   * Listens on changed concrete specification and updates cells
   */
  private void onConcreteSpecificationChanged(Optional<ConcreteSpecification> concreteSpecificationOptional) {

  }

  public TableCategory getView() {
    return tableCategory;
  }
}
