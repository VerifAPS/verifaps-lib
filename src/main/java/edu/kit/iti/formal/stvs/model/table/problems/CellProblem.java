package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.Selection;

/**
 * Created by Philipp on 03.02.2017.
 */
public class CellProblem extends SpecProblem {

  private final int row;
  private final String column;

  public CellProblem(String errorMessage, String column, int row) {
    super(errorMessage, new Selection(column, row));
    this.row = row;
    this.column = column;
  }

  public int getRow() {
    return row;
  }

  public String getColumn() {
    return column;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;
    if (!super.equals(o)) return false;

    CellProblem that = (CellProblem) o;

    if (getRow() != that.getRow()) return false;
    return getColumn() != null ? getColumn().equals(that.getColumn()) : that.getColumn() == null;
  }

  @Override
  public int hashCode() {
    int result = super.hashCode();
    result = 31 * result + getRow();
    result = 31 * result + (getColumn() != null ? getColumn().hashCode() : 0);
    return result;
  }
}
