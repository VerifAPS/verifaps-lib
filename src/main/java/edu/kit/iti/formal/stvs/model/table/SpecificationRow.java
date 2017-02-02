package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableMap;

import java.util.Map;

/**
 * @author Benjamin Alt
 */
public class SpecificationRow<C> implements Commentable {

  private ObservableMap<String, C> cells;
  private StringProperty comment;

  public SpecificationRow(Map<String, C> cells) {
    this.cells = FXCollections.observableMap(cells);
    comment = new SimpleStringProperty();
  }

  public ObservableMap<String,C> getCells() {
    return cells;
  }

  @Override
  public boolean equals(Object obj) {
    if (!(obj instanceof SpecificationRow)) return false;
    if (obj == this) return true;
    SpecificationRow other = (SpecificationRow) obj;
    return this.cells.equals(other.cells);
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
}
