package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.expressions.Value;

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
    return null;
  }
}
