package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.expressions.Value;
import org.apache.commons.lang3.builder.EqualsBuilder;

/**
 * @author Benjamin Alt
 */
public class ConcreteCell {

  private final Value value;

  public ConcreteCell(Value value) {
    this.value = value;
  }

  public Value getValue() {
    return value;
  }

  public String toString() {
    return value.toString();
  }

  @Override
  public boolean equals(Object obj) {
    if (!(obj instanceof ConcreteCell)) return false;
    if (obj == this) return true;
    ConcreteCell other = (ConcreteCell) obj;
    return value.equals(other.value);
  }
}
