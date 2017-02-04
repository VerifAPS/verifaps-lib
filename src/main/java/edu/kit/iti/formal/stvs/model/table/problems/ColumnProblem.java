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
}
