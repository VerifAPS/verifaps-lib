package edu.kit.iti.formal.stvs.model.table;

/**
 * @author Benjamin Alt
 */
public class ConcreteDuration {

  private int duration;
  private int beginCycle;

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
}
