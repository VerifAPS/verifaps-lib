package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import javafx.beans.Observable;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;

/**
 * A specification the cell contents and durations of which are specified by constraints rather than
 * concrete values. This corresponds to a "generalized test table".
 *
 * @author Benjamin Alt
 */
public class ConstraintSpecification extends
    SpecificationTable<SpecIoVariable, ConstraintCell, ConstraintDuration> implements Commentable {

  /**
   * Construct a new specification row containing ConstraintCells.
   *
   * @param initialCells The initial cells, a Map from column identifier to ConstraintCell, with
   *        which to fill the new row
   * @return A SpecificationRow containing the given ConstraintCells
   */
  public static SpecificationRow<ConstraintCell> createRow(
      Map<String, ConstraintCell> initialCells) {
    return new SpecificationRow<>(initialCells,
        cell -> new Observable[] {cell.stringRepresentationProperty(), cell.commentProperty()});
  }

  private final StringProperty comment;
  private final FreeVariableList freeVariableList;
  private final ChangeListener<String> onSpecIoVariableNameChanged;

  /**
   * Construct a new, empty ConstraintSpecification with a default name from an initial list of free
   * variables.
   *
   * @param freeVariableList The initial list of free variables
   */
  public ConstraintSpecification(FreeVariableList freeVariableList) {
    this(DEFAULT_NAME, freeVariableList);
  }

  /**
   * Construct a new, empty ConstraintSpecification with a given name and an initial list of free
   * variables.
   *
   * @param name The name of the ConstraintSpecification
   * @param freeVariableList The list of free variables
   */
  public ConstraintSpecification(String name, FreeVariableList freeVariableList) {
    super(name,
        columnHeader -> new Observable[] {columnHeader.nameProperty(), columnHeader.typeProperty(),
            columnHeader.categoryProperty()},
        durationCell -> new Observable[] {durationCell.stringRepresentationProperty(),
            durationCell.commentProperty()});
    this.onSpecIoVariableNameChanged = this::onSpecIoVariableNameChanged;
    this.freeVariableList = freeVariableList;

    this.comment = new SimpleStringProperty("");
  }

  /**
   * Copy constructor. Creates a deep copy of another ConstraintSpecification.
   *
   * @param sourceSpec The ConstraintSpecification to copy
   */
  public ConstraintSpecification(ConstraintSpecification sourceSpec) {
    this(sourceSpec.getName(), new FreeVariableList(sourceSpec.getFreeVariableList()));
    this.setComment(sourceSpec.getComment());
    for (SpecIoVariable specIoVariable : sourceSpec.getColumnHeaders()) {
      this.getColumnHeaders().add(new SpecIoVariable(specIoVariable));
    }
    for (SpecificationRow<ConstraintCell> row : sourceSpec.getRows()) {
      Map<String, ConstraintCell> clonedCells = new HashMap<>();
      for (String colHeader : row.getCells().keySet()) {
        clonedCells.put(colHeader, new ConstraintCell(row.getCells().get(colHeader)));
      }
      SpecificationRow<ConstraintCell> clonedRow =
          new SpecificationRow<>(clonedCells, row.getExtractor());
      clonedRow.setComment(row.getComment());
      getRows().add(clonedRow);
    }
    for (ConstraintDuration sourceDuration : sourceSpec.getDurations()) {
      getDurations().add(new ConstraintDuration(sourceDuration));
    }
  }

  @Override
  protected void onColumnHeaderAdded(List<? extends SpecIoVariable> added) {
    super.onColumnHeaderAdded(added);
    added.forEach(this::subscribeToIoVariable);
  }

  @Override
  protected void onColumnHeaderRemoved(List<? extends SpecIoVariable> removed) {
    super.onColumnHeaderRemoved(removed);
    removed.forEach(this::unsubscribeFromIoVariable);
  }

  /**
   * Add a listener for name changes to a given {@code SpecIoVariable}.
   *
   * @param specIoVariable The SpecIoVariable to add a name change listener to
   */
  private void subscribeToIoVariable(SpecIoVariable specIoVariable) {
    specIoVariable.nameProperty().addListener(onSpecIoVariableNameChanged);
  }

  /**
   * Remove a listener for name changes from a given {@code SpecIoVariable}.
   *
   * @param specIoVariable The SpecIoVariable to remove a listener from
   */
  private void unsubscribeFromIoVariable(SpecIoVariable specIoVariable) {
    specIoVariable.nameProperty().removeListener(onSpecIoVariableNameChanged);
  }

  private void onSpecIoVariableNameChanged(ObservableValue<? extends String> obs, String nameBefore,
      String nameAfter) {
    for (SpecificationRow<ConstraintCell> row : getRows()) {
      ConstraintCell entry = row.getCells().get(nameBefore);
      if (entry != null) {
        row.getCells().put(nameAfter, entry);
        row.getCells().remove(nameBefore);
      }
    }
  }

  @Override
  public void setComment(String comment) {
    this.comment.set(comment);
  }

  @Override
  public String getComment() {
    return comment.get();
  }

  @Override
  public StringProperty commentProperty() {
    return comment;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null || getClass() != obj.getClass()) {
      return false;
    }
    if (!super.equals(obj)) {
      return false;
    }

    ConstraintSpecification that = (ConstraintSpecification) obj;

    if (getComment() != null ? !getComment().equals(that.getComment())
        : that.getComment() != null) {
      return false;
    }
    return getFreeVariableList() != null ? getFreeVariableList().equals(that.getFreeVariableList())
        : that.getFreeVariableList() == null;
  }

  @Override
  public int hashCode() {
    int result = super.hashCode();
    result = 31 * result + (getComment() != null ? getComment().hashCode() : 0);
    result = 31 * result + (getFreeVariableList() != null ? getFreeVariableList().hashCode() : 0);
    return result;
  }

  public FreeVariableList getFreeVariableList() {
    return freeVariableList;
  }
}
