package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.expressions.Value;
import javafx.beans.property.ReadOnlyStringProperty;
import javafx.beans.property.SimpleStringProperty;

/**
 * @author Benjamin Alt
 */
public class ConcreteCell implements StringReadable {

  private final Value value;
  private final ReadOnlyStringProperty stringProperty;

  public ConcreteCell(Value value) {
    this.value = value;
    this.stringProperty = new SimpleStringProperty(value.toString());
  }

  public Value getValue() {
    return value;
  }

  @Override
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

  @Override
  public String getAsString() {
    return toString();
  }

  @Override
  public ReadOnlyStringProperty stringRepresentationProperty() {
    return stringProperty;
  }
}
