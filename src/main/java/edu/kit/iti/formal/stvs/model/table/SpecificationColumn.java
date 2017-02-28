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
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }

    SpecificationColumn<?> that = (SpecificationColumn<?>) o;

    if (cells != null ? !cells.equals(that.cells) : that.cells != null) {
      return false;
    }
    return comment != null ? comment.get().equals(that.comment.get()) : that.comment == null;

  }

  public String toString() {
    return "SpecificationColumn(cells: " + cells + ", comment: " + comment.get() + ")";
  }
}
