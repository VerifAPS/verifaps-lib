package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.Selection;

/**
 * Created by Philipp on 03.02.2017.
 */
public abstract class ColumnProblem extends SpecProblem {

  private final String column;

  public ColumnProblem(String errorMessage, String column) {
    super(errorMessage, new Selection(column));
    this.column = column;
  }

  public String getColumn() {
    return column;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    if (!super.equals(o)) return false;

    ColumnProblem that = (ColumnProblem) o;

    return getColumn() != null ? getColumn().equals(that.getColumn()) : that.getColumn() == null;
  }

  @Override
  public int hashCode() {
    int result = super.hashCode();
    result = 31 * result + (getColumn() != null ? getColumn().hashCode() : 0);
    return result;
  }
}
