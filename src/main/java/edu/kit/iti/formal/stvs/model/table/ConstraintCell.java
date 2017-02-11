package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import org.apache.commons.lang3.builder.EqualsBuilder;

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

  @Override
  public boolean equals(Object obj) {
    if (!(obj instanceof ConstraintCell)) return false;
    if (obj == this) return true;
    ConstraintCell other = (ConstraintCell) obj;
    return new EqualsBuilder().
        append(stringRepresentation.get(), other.stringRepresentation.get()).
        append(comment.get(), other.comment.get()).
        isEquals();
  }

  public String toString() {
    return "ConstraintCell(" + getAsString() + ", comment: " + getComment() + ")";
  }

}
