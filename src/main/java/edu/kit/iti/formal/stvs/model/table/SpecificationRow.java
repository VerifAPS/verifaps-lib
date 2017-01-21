package edu.kit.iti.formal.stvs.model.table;

import java.util.Map;
import java.util.NoSuchElementException;

/**
 * @author Benjamin Alt
 */
public class SpecificationRow<C, D> {

  private final D duration;
  private final Map<String, C> cells;

  public SpecificationRow(D duration, Map<String, C> cells) {
    this.duration = duration;
    this.cells = cells;
  }

  public C getCellForVariable(String variable) {
    C cell = cells.get(variable);
    if (cell == null) {
      throw new NoSuchElementException("Cannot get cell for variable " + variable + " : No such variable");
    }
    return cell;
  }

  public D getDuration() {
    return duration;
  }
}
