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
}
