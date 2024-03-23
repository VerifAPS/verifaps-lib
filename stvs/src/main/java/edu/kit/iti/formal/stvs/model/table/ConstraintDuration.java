package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import org.apache.commons.lang3.builder.EqualsBuilder;

/**
 * An abstract duration given by a constraint rather than a concrete value. For the grammar of
 * constraint durations, see https://git.scc.kit.edu/peese/stverificationstudio/issues/25.
 *
 * @author Benjamin Alt
 */
public class ConstraintDuration implements CellOperationProvider {

  private StringProperty stringRepresentation;
  private StringProperty comment;

  /**
   * Construct a new ConstraintDuration from its string representation (i.e. the constraint as
   * string).
   *
   * @param stringRepresentation A string representation of the constraint duration
   */
  public ConstraintDuration(String stringRepresentation) {
    this.comment = new SimpleStringProperty();
    this.stringRepresentation = new SimpleStringProperty(stringRepresentation);
  }

  public ConstraintDuration(ConstraintDuration sourceDuration) {
    this(sourceDuration.getAsString());
    setComment(sourceDuration.getComment());
  }

  @Override
  public String getAsString() {
    return this.stringRepresentation.get();
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
    if (this == obj) {
      return true;
    }
    if (obj == null || getClass() != obj.getClass()) {
      return false;
    }

    ConstraintDuration that = (ConstraintDuration) obj;

    if ((getAsString() != null)
        ? !getAsString().equals(that.getAsString()) : (that.getAsString() != null)) {
      return false;
    }
    return (getComment() != null)
        ? getComment().equals(that.getComment()) : (that.getComment() == null);
  }

  @Override
  public int hashCode() {
    int result = getAsString() != null ? getAsString().hashCode() : 0;
    result = 31 * result + (getComment() != null ? getComment().hashCode() : 0);
    return result;
  }

  public String toString() {
    return debuggingString();
  }
}
