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
    if (!(obj instanceof ConstraintDuration)) {
      return false;
    }
    if (obj == this) {
      return true;
    }
    ConstraintDuration other = (ConstraintDuration) obj;
    return new EqualsBuilder().append(stringRepresentation.get(), other.stringRepresentation.get())
        .append(comment.get(), other.comment.get()).isEquals();
  }

  public String toString() {
    return debuggingString();
  }
}
