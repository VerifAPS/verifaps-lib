package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval;
import edu.kit.iti.formal.stvs.model.expressions.parser.IntervalParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;

/**
 * <p>The abstract model for problems that occurred in duration cells.</p>
 *
 * <p>Created by Philipp on 03.02.2017.</p>
 *
 * @author Philipp
 */
public abstract class DurationProblem extends SpecProblem {

  private final int row;

  /**
   * <p>Creates a duration problem with given error message (used for error tooltips in the
   * GUI).</p>
   *
   * @param errorMessage the error message (used for viewing error tooltips)
   * @param row the row in which the problem occurred
   */
  public DurationProblem(String errorMessage, int row) {
    super(errorMessage, new Selection("duration", row));
    this.row = row;
  }

  public int getRow() {
    return row;
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

    DurationProblem that = (DurationProblem) obj;

    return getRow() == that.getRow();
  }

  @Override
  public int hashCode() {
    int result = super.hashCode();
    result = 31 * result + getRow();
    return result;
  }
}
