package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import javafx.beans.Observable;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;

import java.util.List;
import java.util.Map;

/**
 * @author Benjamin Alt
 */
public class ConstraintSpecification extends SpecificationTable<SpecIoVariable, ConstraintCell, ConstraintDuration> implements Commentable {

  public static SpecificationRow<ConstraintCell> createRow(
      Map<String, ConstraintCell> wildcardCells) {
    return new SpecificationRow<>(wildcardCells,
        cell -> new Observable[] {
            cell.stringRepresentationProperty(),
            cell.commentProperty()
        });
  }

  private final StringProperty comment;
  private final FreeVariableList freeVariableList;
  private final ChangeListener<String> onSpecIoVariableNameChanged = this::onSpecIoVariableNameChanged;

  public ConstraintSpecification(FreeVariableList freeVariableList) {
    super(durationCell -> new Observable[] {
        durationCell.stringRepresentationProperty(),
        durationCell.commentProperty()
    });
    this.freeVariableList = freeVariableList;

    this.comment = new SimpleStringProperty("");
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

  private void subscribeToIoVariable(SpecIoVariable specIoVariable) {
    specIoVariable.nameProperty().addListener(onSpecIoVariableNameChanged);
  }

  private void unsubscribeFromIoVariable(SpecIoVariable specIoVariable) {
    specIoVariable.nameProperty().removeListener(onSpecIoVariableNameChanged);
  }

  private void onSpecIoVariableNameChanged(
      ObservableValue<? extends String> obs,
      String nameBefore,
      String nameAfter) {
    for (SpecificationRow<ConstraintCell> row : getRows()) {
      ConstraintCell entry = row.getCells().get(nameBefore);
      if (entry != null) {
        row.getCells().put(nameAfter, entry);
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
  public boolean equals(Object o) {
    if (this == o) return true;
    if (!(o instanceof ConstraintSpecification)) return false;
    if (!super.equals(o)) return false;

    ConstraintSpecification that = (ConstraintSpecification) o;

    return comment != null ? comment.get().equals(that.comment.get()) : that.comment == null;
  }

  @Override
  public int hashCode() {
    return comment != null ? comment.hashCode() ^ super.hashCode() : super.hashCode();
  }

  public FreeVariableList getFreeVariableList() {
    return freeVariableList;
  }
}
