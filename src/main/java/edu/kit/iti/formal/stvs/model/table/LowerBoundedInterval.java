package edu.kit.iti.formal.stvs.model.table;

import java.util.Optional;

/**
 * @author Benjamin Alt
 */
public class LowerBoundedInterval {
  private int lowerBound;
  private Optional<Integer> upperBound;

  public LowerBoundedInterval(int lowerBound, Optional<Integer> upperBound) {
    this.lowerBound = lowerBound;
    this.upperBound = upperBound;
  }
}
