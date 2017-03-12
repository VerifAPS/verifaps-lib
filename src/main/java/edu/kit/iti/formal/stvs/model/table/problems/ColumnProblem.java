package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.Selection;

/**
 * A {@link SpecProblem} concerning columns.
 *
 * @author Philipp
 */
public abstract class ColumnProblem extends SpecProblem {

  private final String column;

  /**
   * Create a new ColumnProblem with a given error message and for a given column.
   * @param errorMessage The error message
   * @param column The header name of the problematic column
   */
  public ColumnProblem(String errorMessage, String column) {
    super(errorMessage, new Selection(column));
    this.column = column;
  }

  public String getColumn() {
    return column;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null || getClass() != obj.getClass()) {
      return false;
    }
    if (!super.equals(obj)) {
      return false;
    }

    ColumnProblem that = (ColumnProblem) obj;

    return getColumn() != null ? getColumn().equals(that.getColumn()) : that.getColumn() == null;
  }

  @Override
  public int hashCode() {
    int result = super.hashCode();
    result = 31 * result + (getColumn() != null ? getColumn().hashCode() : 0);
    return result;
  }
}
