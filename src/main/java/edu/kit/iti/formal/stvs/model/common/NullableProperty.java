package edu.kit.iti.formal.stvs.model.common;

import javafx.beans.property.SimpleObjectProperty;

/**
 * A property the value of which may be null.
 *
 * @author Lukas Fritsch
 */
public class NullableProperty<T> extends SimpleObjectProperty<T> {

  /**
   * Create a new NullableProperty from an initial value.
   * @param initial The initial value
   */
  public NullableProperty(T initial) {
    super(initial);
  }

  /**
   * Create a new NullableProperty with an empty initial value; the value of the property is set
   * to null.
   */
  public NullableProperty() {
    super(null);
  }
}
