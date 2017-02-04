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
}
