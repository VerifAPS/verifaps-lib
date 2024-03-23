package edu.kit.iti.formal.stvs.model.table;

import org.apache.commons.lang3.builder.EqualsBuilder;

/**
 * A concrete duration. A ConcreteDuration is localized in time, i.e. it is aware of the cycle in
 * which it begins.
 *
 * @author Benjamin Alt
 */
public class ConcreteDuration {

  private int duration;
  private int beginCycle;

  /**
   * Construct a new concrete duration.
   *
   * @param beginCycle The cycle in which this duration begins
   * @param duration The duration
   */
  public ConcreteDuration(int beginCycle, int duration) {
    if (beginCycle < 0) {
      throw new IllegalArgumentException("BeginCycle must be nonnegative");
    }
    if (duration < 0) {
      throw new IllegalArgumentException("Duration must me nonnegative");
    }
    this.beginCycle = beginCycle;
    this.duration = duration;
  }

  public int getDuration() {
    return duration;
  }

  public int getBeginCycle() {
    return beginCycle;
  }

  public int getEndCycle() {
    return beginCycle + duration;
  }

  public String toString() {
    return Integer.toString(duration);
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }

    ConcreteDuration duration1 = (ConcreteDuration) o;

    if (getDuration() != duration1.getDuration()) {
      return false;
    }
    return getBeginCycle() == duration1.getBeginCycle();
  }

  @Override
  public int hashCode() {
    int result = getDuration();
    result = 31 * result + getBeginCycle();
    return result;
  }
}
