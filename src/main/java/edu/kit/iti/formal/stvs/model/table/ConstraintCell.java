package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

/**
 * @author Benjamin Alt
 */
public class ConstraintCell implements CellOperationProvider {

  private StringProperty stringRepresentation;
  private StringProperty comment;

  public ConstraintCell(String stringRepresentation) {
    this.stringRepresentation = new SimpleStringProperty(stringRepresentation);
    this.comment = new SimpleStringProperty();
  }

  @Override
  public String getAsString() {
    return stringRepresentation.get();
  }

  @Override
  public void setFromString(String stringRepresentation) {
    this.stringRepresentation.set(stringRepresentation);
  }

  @Override
  public StringProperty stringRepresentationProperty() {
    return stringRepresentation;
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
}
