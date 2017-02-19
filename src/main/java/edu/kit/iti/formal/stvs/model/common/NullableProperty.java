package edu.kit.iti.formal.stvs.model.common;

import javafx.beans.property.SimpleObjectProperty;

/**
 * Created by Lukas on 19.01.2017.
 * @author Lukas Fritsch
 */
public class NullableProperty<T> extends SimpleObjectProperty<T> {
  public NullableProperty(T initial) {
    super(initial);
  }

  public NullableProperty() {
    super(null);
  }
}
