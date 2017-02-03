package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableMap;

import java.util.Map;
import java.util.stream.Collectors;

/**
 * @author Benjamin Alt
 */
public class SpecificationRow<C> implements Commentable {

  private ObservableMap<String, C> cells;
  private StringProperty comment;

  public SpecificationRow(Map<String, C> cells) {
    this.cells = FXCollections.observableMap(cells);
    comment = new SimpleStringProperty("");
  }

  public ObservableMap<String,C> getCells() {
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
    return comment;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (!(o instanceof SpecificationRow)) return false;

    SpecificationRow<?> that = (SpecificationRow<?>) o;

    if (!cells.equals(that.cells)) return false;
    return comment != null ? comment.get().equals(that.comment.get()) : that.comment == null;
  }

  @Override
  public int hashCode() {
    int result = cells.hashCode();
    result = 31 * result + (comment != null ? comment.hashCode() : 0);
    return result;
  }

  public String toString() {
    String map =
        String.join(", ",
            cells.entrySet().stream().map(entry ->
                entry.getKey() + ": " + entry.getValue()).collect(Collectors.toList()));
    return "SpecificationRow(comment: " + getComment() + ", " + map + ")";
  }
}
