package edu.kit.iti.formal.stvs.model.table;

import java.util.Map;
import java.util.NoSuchElementException;

/**
 * @author Benjamin Alt
 */
public class SpecificationRow<C> {

  protected final Map<String, C> cells;

  public SpecificationRow(Map<String, C> cells) {
    this.cells = cells;
  }

  public C getCellForVariable(String variable) {
    C cell = cells.get(variable);
    if (cell == null) {
      throw new NoSuchElementException("Cannot get cell for variable " + variable + " : No such variable");
    }
    return cell;
  }

  @Override
  public boolean equals(Object obj) {
    if (!(obj instanceof SpecificationRow)) return false;
    if (obj == this) return true;
    SpecificationRow other = (SpecificationRow) obj;
    return this.cells.equals(other.cells);
  }
}
