package edu.kit.iti.formal.stvs.model.table;

import java.util.List;

import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

/**
 * A column in a specification (see {@link SpecificationTable}). The generic type parameter C is the
 * type of the cells.
 *
 * @author Benjamin Alt
 */
public class SpecificationColumn<C> implements Commentable {

  private List<C> cells;
  private StringProperty comment;

  /**
   * Create a new SpecificationColumn fro a list of cells.
   *
   * @param cells The cells for this column.
   */
  public SpecificationColumn(List<C> cells) {
    this.cells = cells;
    this.comment = new SimpleStringProperty("");
  }

  public List<C> getCells() {
    return cells;
  }

  @Override
  public void setComment(String comment) {
    this.comment.set(comment);
  }

  @Override
  public String getComment() {
    return this.comment.get();
  }

  @Override
  public StringProperty commentProperty() {
    return this.comment;
  }

  @Override
  public int hashCode() {
    int result = getCells() != null ? getCells().hashCode() : 0;
    result = 31 * result + (getComment() != null ? getComment().hashCode() : 0);
    return result;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null || getClass() != obj.getClass()) {
      return false;
    }

    SpecificationColumn<?> that = (SpecificationColumn<?>) obj;

    if ((getCells() != null)
        ? !getCells().equals(that.getCells()) : (that.getCells() != null)) {
      return false;
    }
    return (getComment() != null
        ? getComment().equals(that.getComment()) : that.getComment() == null);
  }

  @Override
  public String toString() {
    return "SpecificationColumn(cells: " + cells + ", comment: " + comment.get() + ")";
  }
}
