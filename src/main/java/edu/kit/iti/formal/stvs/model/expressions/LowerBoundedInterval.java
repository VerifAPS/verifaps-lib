package edu.kit.iti.formal.stvs.model.expressions;

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

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (!(o instanceof LowerBoundedInterval)) return false;

    LowerBoundedInterval that = (LowerBoundedInterval) o;

    if (lowerBound != that.lowerBound) return false;
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
    return "LowerBoundedInterval(" + lowerBound + "," +
        (upperBound.isPresent() ? upperBound.get() : "-") +
        ")";
  }
}
