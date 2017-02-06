package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.Selection;

/**
 * Created by Philipp on 03.02.2017.
 */
public abstract class DurationProblem extends SpecProblem {

  private final int row;

  public DurationProblem(String errorMessage, int row) {
    super(errorMessage, new Selection("duration", row));
    this.row = row;
  }

  public int getRow() {
    return row;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    if (!super.equals(o)) return false;

    DurationProblem that = (DurationProblem) o;

    return getRow() == that.getRow();
  }

  @Override
  public int hashCode() {
    int result = super.hashCode();
    result = 31 * result + getRow();
    return result;
  }
}
