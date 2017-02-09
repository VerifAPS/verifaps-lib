package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import javafx.beans.Observable;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

import java.util.Map;

/**
 * @author Benjamin Alt
 */
public class ConstraintSpecification extends SpecificationTable<SpecIoVariable, ConstraintCell, ConstraintDuration> implements Commentable {

  public static SpecificationRow<ConstraintCell> createRow(
      Map<String, ConstraintCell> wildcardCells) {
    return new SpecificationRow<>(wildcardCells,
        cell -> new Observable[] { cell.stringRepresentationProperty() });
  }

  private final StringProperty comment;
  private final FreeVariableList freeVariableList;

  public ConstraintSpecification(FreeVariableList freeVariableList) {
    super(durationCell -> new Observable[] { durationCell.stringRepresentationProperty() });
    this.freeVariableList = freeVariableList;

    this.comment = new SimpleStringProperty("");
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
