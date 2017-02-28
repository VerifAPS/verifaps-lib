package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.expressions.LowerBoundedInterval;
import edu.kit.iti.formal.stvs.model.expressions.parser.IntervalParser;
import edu.kit.iti.formal.stvs.model.expressions.parser.ParseException;
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;

/**
 * Created by Philipp on 03.02.2017.
 *
 * @author Philipp
 */
public abstract class DurationProblem extends SpecProblem {

  public static LowerBoundedInterval tryParseDuration(int row, ConstraintDuration duration)
      throws DurationProblem {
    try {
      return IntervalParser.parse(duration.getAsString());
    } catch (ParseException parseException) {
      throw new DurationParseProblem(parseException, row);
    }
  }

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
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }
    if (!super.equals(o)) {
      return false;
    }

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
