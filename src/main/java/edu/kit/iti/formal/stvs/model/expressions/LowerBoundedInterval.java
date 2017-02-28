package edu.kit.iti.formal.stvs.model.expressions;

import java.util.Optional;

/**
 * The runtime representation for intervals that possibly have no
 * upper bound, but have a guaranteed lower bound.
 *
 * @author Benjamin Alt
 */
public class LowerBoundedInterval {
  public int getLowerBound() {
    return lowerBound;
  }

  public Optional<Integer> getUpperBound() {
    return upperBound;
  }

  private int lowerBound;
  private Optional<Integer> upperBound;

  /**
   * @param lowerBound the lower bound for this interval
   * @param upperBound the optional upper bound for this interval
   */
  public LowerBoundedInterval(int lowerBound, Optional<Integer> upperBound) {
    this.lowerBound = lowerBound;
    this.upperBound = upperBound;
  }

  @Override
  public boolean equals(Object other) {
    if (this == other) {
      return true;
    }
    if (!(other instanceof LowerBoundedInterval)) {
      return false;
    }

    LowerBoundedInterval that = (LowerBoundedInterval) other;

    if (lowerBound != that.lowerBound) {
      return false;
    }
    return upperBound.equals(that.upperBound);
  }

  @Override
  public int hashCode() {
    int result = lowerBound;
    result = 31 * result + upperBound.hashCode();
    return result;
  }

  @Override
  public String toString() {
    return "LowerBoundedInterval(" + lowerBound + ","
        + (upperBound.isPresent() ? upperBound.get() : "-")
        + ")";
  }
}
