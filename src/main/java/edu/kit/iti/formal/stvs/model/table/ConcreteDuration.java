package edu.kit.iti.formal.stvs.model.table;

import org.apache.commons.lang3.builder.EqualsBuilder;

/**
 * A concrete duration. A ConcreteDuration is localized in time, i.e. it is aware of the cycle in
 * which it begins.
 * @author Benjamin Alt
 */
public class ConcreteDuration {

  private int duration;
  private int beginCycle;

  /**
   * Construct a new concrete duration.
   * @param beginCycle The cycle in which this duration begins
   * @param duration The duration
   */
  public ConcreteDuration(int beginCycle, int duration) {
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
  public boolean equals(Object obj) {
    if (!(obj instanceof ConcreteDuration)) return false;
    if (obj == this) return true;
    ConcreteDuration other = (ConcreteDuration) obj;
    return new EqualsBuilder().
        append(duration, other.duration).
        append(beginCycle, other.beginCycle).
        isEquals();
  }
}
