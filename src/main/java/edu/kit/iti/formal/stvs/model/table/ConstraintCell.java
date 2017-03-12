package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import org.apache.commons.lang3.builder.EqualsBuilder;

/**
 * A cell containing constraint expression (for the syntax, see
 * https://git.scc.kit.edu/peese/stverificationstudio/issues/25). The cells in a
 * {@link ConstraintSpecification} are of this type.
 *
 * @author Benjamin Alt
 */
public class ConstraintCell implements CellOperationProvider {

  private StringProperty stringRepresentation;
  private StringProperty comment;

  /**
   * Construct a new ConstraintCell from a string representation of its contents (i.e. of a
   * constraint expression).
   *
   * @param stringRepresentation The string representation of a constraint expression
   */
  public ConstraintCell(String stringRepresentation) {
    this.stringRepresentation = new SimpleStringProperty(stringRepresentation);
    this.comment = new SimpleStringProperty();
  }

  /**
   * Copy constructor; performs a deep copy of a given ConstraintCell.
   *
   * @param constraintCell The ConstraintCell to copy
   */
  public ConstraintCell(ConstraintCell constraintCell) {
    this(constraintCell.getAsString());
    this.setComment(constraintCell.getComment());
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
    if (this == obj) {
      return true;
    }
    if (obj == null || getClass() != obj.getClass()) {
      return false;
    }

    ConstraintCell that = (ConstraintCell) obj;

    if (getAsString() != null) {
      if (!getAsString().equals(
          that.getAsString())) {
        return false;
      }
    } else {
      if ((that.getAsString() != null)) {
        return false;
      }
    }
    return getComment() != null
        ? getComment().equals(that.getComment()) : that.getComment() == null;
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
