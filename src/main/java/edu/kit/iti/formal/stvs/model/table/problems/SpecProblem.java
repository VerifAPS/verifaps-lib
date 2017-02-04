package edu.kit.iti.formal.stvs.model.table.problems;

import edu.kit.iti.formal.stvs.model.common.Selection;

public abstract class SpecProblem extends Exception {

  private final String errorMessage;
  private final Selection location;

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
}
