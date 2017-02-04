package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

import java.util.List;

/**
 * @author Benjamin Alt
 */
public class SpecificationColumn<C> implements Commentable {

  private List<C> cells;
  private StringProperty comment;

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
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;

    SpecificationColumn<?> that = (SpecificationColumn<?>) o;

    if (cells != null ? !cells.equals(that.cells) : that.cells != null) return false;
    return comment != null ? comment.get().equals(that.comment.get()) : that.comment == null;

  }

  @Override
  public int hashCode() {
    int result = cells != null ? cells.hashCode() : 0;
    result = 31 * result + (comment != null ? comment.hashCode() : 0);
    return result;
  }

  public String toString() {
    return "SpecificationColumn(cells: " + cells + ", comment: " + comment.get() + ")";
  }
}
