package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.Selection;

/*
 * A problem concerning a specification table.
 * @author Philipp
 */
public abstract class SpecProblem extends Exception {

  private final String errorMessage;
  private final Selection location;

  /**
   * Create a new SpecProblem with a given error message and for a given location.
   * @param errorMessage The error message
   * @param location The location of the problem
   */
  public SpecProblem(String errorMessage, Selection location) {
    super(errorMessage);
    this.errorMessage = errorMessage;
    this.location = location;
  }

  public String getErrorMessage() {
    return this.errorMessage;
  }

  public Selection getLocation() {
    return location;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }

    SpecProblem that = (SpecProblem) o;

    if (getErrorMessage() != null ? !getErrorMessage().equals(that.getErrorMessage())
        : that.getErrorMessage() != null) {
      return false;
    }
    return getLocation() != null ? getLocation().equals(that.getLocation())
        : that.getLocation() == null;
  }

  @Override
  public int hashCode() {
    int result = getErrorMessage() != null ? getErrorMessage().hashCode() : 0;
    result = 31 * result + (getLocation() != null ? getLocation().hashCode() : 0);
    return result;
  }
}
