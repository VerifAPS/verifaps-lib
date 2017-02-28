package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.Selection;

/**
 * <p>Models problems in cells. Used for rendering in the view (see
 * {@link edu.kit.iti.formal.stvs.view.spec.table.SpecificationTableCell}).</p>
 *
 * <p>Created by Philipp on 03.02.2017.</p>
 *
 * @author Philipp
 */
public class CellProblem extends SpecProblem {

  private final int row;
  private final String column;

  /**
   * <p>Constructor for a problem that has an error message and a position inside a table.</p>
   *
   * @param errorMessage the error message to show as a tooltip in view
   * @param column the column of the problematic cell
   * @param row the row of the problematic cell
   */
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

    CellProblem that = (CellProblem) obj;

    if (getRow() != that.getRow()) {
      return false;
    }
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
