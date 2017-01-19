package edu.kit.iti.formal.stvs.model.common;

import javafx.beans.property.Property;
import javafx.beans.property.ObjectPropertyBase;

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
  public Object getBean() {
    return property.getBean();
  }

  /**
   * Returns the name of this property. If the property does not have a name,
   * this method returns an empty {@code String}.
   *
   * @return the name or an empty {@code String}
   */
  @Override
  public String getName() {
    return "";
  }

  /**
   * Creates an property that wraps an existing property and adds
   * the possibility of an absent value.
   *
   * @param property Property to be wrapped
   */
  public OptionalPropertyBase(R property) {
    super(property.getValue());
    this.name = "";
    this.property = property;
  }

  /**
   * Copy of {@link OptionalPropertyBase#set(Object)}.
   *
   * @param value Value that the property should be set to
   * @see OptionalPropertyBase#set
   */
  @Override
  public void setValue(S value) {
    set(value);
  }

  /**
   * Set this property to a given value.
   * If the value is null the inner property is not touched.
   *
   * @param value Value that the property should be set to
   */
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

  /**
   * Wraps a property into an {@link OptionalPropertyBase} and sets its value to null.
   *
   * @param property Property to be wrapped
   * @param <S> Type of the object wrapped in {@code property}
   * @param <R> Type of the {@code property}
   * @return optional Propertie wrapping {@code property}
   */
  public static <S, R extends Property<S>> OptionalPropertyBase<S, R> ofNull(R property) {
    OptionalPropertyBase<S, R> optionalPropertyBase = new OptionalPropertyBase<>(property);
    optionalPropertyBase.clear();
    return optionalPropertyBase;
  }
}
