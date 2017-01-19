package edu.kit.iti.formal.stvs.model.table;


import java.util.Map;

/**
 * Created by philipp on 09.01.17.
 */
public class SpecificationRow<C, D> {

  private final D duration;
  private final Map<String, C> cells;

  public SpecificationRow(D duration, Map<String, C> cells) {
    this.duration = duration;
    this.cells = cells;
  }

  public C getEntryForVariable(String variable) {
    return null;
  }

  public D getDuration() {
    return duration;
  }
}
