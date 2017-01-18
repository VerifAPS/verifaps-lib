package edu.kit.iti.formal.stvs.model.common;

import javafx.beans.property.ObjectPropertyBase;
import javafx.beans.property.Property;

/**
 * Created by leonk on 17.01.2017.
 */
public class OptionalPropertyBase<S, R extends Property<S>> extends ObjectPropertyBase<S> {
  private final String name;
  private final R property;

  /**
   * Returns the {@code Object} that contains this property. If this property
   * is not contained in an {@code Object}, {@code null} is returned.
   *
   * @return the containing {@code Object} or {@code null}
   */
  @Override
  public Property<S> getBean() {
    return property;
  }

  /**
   * Returns the name of this property. If the property does not have a name,
   * this method returns an empty {@code String}.
   *
   * @return the name or an empty {@code String}
   */
  @Override
  public String getName() {
    return name;
  }

  public OptionalPropertyBase(R property) {
    super(property.getValue());
    this.name = "";
    this.property = property;
  }

  public OptionalPropertyBase(R property, String name) {
    super(property.getValue());
    this.name = name;
    this.property = property;
  }

  @Override
  public void setValue(S value) {
    set(value);
  }

  @Override
  public void set(S value) {
    super.set(value);
    if (value != null) {
      property.setValue(value);
    }
  }

  public R getProperty() {
    return property;
  }

  public void clear() {
    set(null);
  }

}
