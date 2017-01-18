package edu.kit.iti.formal.stvs.model.common;

import javafx.beans.property.ObjectPropertyBase;
import javafx.beans.property.Property;
import javafx.beans.property.StringProperty;

/**
 * Created by leonk on 17.01.2017.
 */
public class OptionalProperty<R> extends OptionalPropertyBase<R,Property<R>>{
  public OptionalProperty(Property<R> property) {
    super(property);
  }
}