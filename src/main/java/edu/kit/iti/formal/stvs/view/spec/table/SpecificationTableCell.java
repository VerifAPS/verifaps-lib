package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.table.HybridCell;
import edu.kit.iti.formal.stvs.model.table.HybridRow;
import edu.kit.iti.formal.stvs.model.table.problems.CellProblem;
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator;
import edu.kit.iti.formal.stvs.model.table.problems.DurationProblem;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import edu.kit.iti.formal.stvs.view.ViewUtils;

import java.util.List;
import java.util.stream.Collectors;

import javafx.scene.control.Label;
import javafx.scene.control.Tooltip;
import javafx.scene.control.cell.TextFieldTableCell;
import javafx.scene.layout.VBox;
import javafx.util.converter.DefaultStringConverter;

/**
 * The view for a cell in a specification table.
 *
 * @author Philipp
 */
public class SpecificationTableCell extends AdvancedTextFieldTableCell<HybridRow, String> {

  private final ConstraintSpecificationValidator validator;

  /**
   * Create a new SpecificationTableCell with a given validator.
   * @param validator The validator for this cell
   */
  public SpecificationTableCell(ConstraintSpecificationValidator validator) {
    super(new DefaultStringConverter());
    this.validator = validator;

    validator.problemsProperty().addListener(observable -> this.onProblemsChanged());
    emptyProperty().addListener(observable -> this.onProblemsChanged());
    getStyleClass().add("spec-cell");
    ViewUtils.setupId(this);
    onProblemsChanged();
  }

  @Override
  public void updateItem(String item, boolean empty) {
    super.updateItem(item, empty);
    if (!empty && getCellModel() != null) {
      List<String> counterExampleCells = getCellModel().counterExamplesProperty();
      VBox counterExampleLabels = new VBox();
      counterExampleLabels.getChildren().addAll(counterExampleCells.stream().map(text -> {
        Label label = new Label(text);
        label.getStyleClass().add("spec-counterexample");
        return label;
      }).collect(Collectors.toList()));
      setGraphic(counterExampleLabels);
    }
  }

  private void configureProblem(SpecProblem problem) {
    getStyleClass().remove("spec-cell-problem");
    getStyleClass().add("spec-cell-problem");
    setTooltip(new Tooltip(problem.getErrorMessage()));
  }

  private void resetCellVisuals() {
    getStyleClass().remove("spec-cell-problem");
    setTooltip(null);
  }

  private void onProblemsChanged() {
    if (!isEmpty()) {
      List<SpecProblem> problems = validator.problemsProperty().get();
      for (SpecProblem problem : problems) {
        if (problem instanceof CellProblem && !isDurationCell()) {
          CellProblem cellProblem = (CellProblem) problem;
          String col = cellProblem.getColumn();
          if (col.equals(getColumnId()) && cellProblem.getRow() == getRowIndex()) {
            configureProblem(problem);
            return;
          }
        } else if (problem instanceof DurationProblem) {
          DurationProblem durationProblem = (DurationProblem) problem;
          if (durationProblem.getRow() == getRowIndex()) {
            configureProblem(problem);
            return;
          }
        }
      }
    }
    resetCellVisuals();
  }

  private HybridCell<?> getCellModel() {
    if (getTableRow() == null) {
      return null;
    }
    HybridRow row = (HybridRow) getTableRow().getItem();
    if (row == null) {
      return null;
    }
    String columnId = (String) getTableColumn().getUserData();
    if (columnId != null) {
      return row.getCells().get(columnId);
    } else { // we are a duration cell
      return row.getDuration();
    }
  }

  private boolean isDurationCell() {
    return getTableColumn().getUserData() == null;
  }

  private String getColumnId() {
    return (String) getTableColumn().getUserData();
  }

  private int getRowIndex() {
    return getTableRow().getIndex();
  }
}
