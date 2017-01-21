package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.Value;
import javafx.beans.property.*;

/**
 * Created by csicar on 10.01.17.
 */
public class FreeVariable {
  private final StringProperty name;
  private final ObjectProperty<Type> type;
  private final ObjectProperty<Value> defaultValue;

  /**
   * Creates a free variable with a name and type.
   * A default value will be generated through {@link Type#generateDefaultValue()}.
   *
   * @param name Name of the free variable
   * @param type Type of the free variable
   */
  public FreeVariable(String name, Type type) {
    this.name = new SimpleStringProperty(name);
    this.type = new SimpleObjectProperty<>(type);
    this.defaultValue = new SimpleObjectProperty<>(type.generateDefaultValue());
  }

  /**
   * Creates a free variable with a name, type and default value.
   *
   * @param name         Name of the free variable
   * @param type         Type of the free variable
   * @param defaultValue Default value of the free variable
   * @throws IllegalValueTypeException thrown if {@link Type}
   *                                   of {@code defaultValue} does not match {@code type}
   */
  public FreeVariable(String name, Type type, Value defaultValue) throws IllegalValueTypeException {
    this.name = new SimpleStringProperty(name);
    this.type = new SimpleObjectProperty<>(type);
    if (!defaultValue.getType().checksAgainst(type)) {
      throw new IllegalValueTypeException(defaultValue, type, "DefaultValue has wrong type.");
    }
    this.defaultValue = new SimpleObjectProperty<>(defaultValue);
  }

  public String getName() {
    return name.get();
  }

  public StringProperty nameProperty() {
    return name;
  }

  /**
   * Rename the variable.
   *
   * @param name New name for the free variable
   */
  public void setName(String name) {
    this.name.set(name);
  }

  public Type getType() {
    return type.get();
  }

  public ReadOnlyObjectProperty<Type> typeProperty() {
    return type;
  }

  /**
   * Sets the type of this variable.
   * If the current value has a different type, the value is replaced with
   * {@link Type#generateDefaultValue()}
   *
   * @param type New type for the free variable
   */
  public void setType(Type type) {
    this.type.set(type);
    if (!this.defaultValue.get().getType().checksAgainst(type)) {
      this.defaultValue.set(type.generateDefaultValue());
    }
  }

  public Value getDefaultValue() {
    return defaultValue.get();
  }

  public ReadOnlyObjectProperty<Value> defaultValueProperty() {
    return defaultValue;
  }

  /**
   * Assigns a new value to the free variable.
   *
   * @param defaultValue New default value for the free variable
   * @throws IllegalValueTypeException thrown if {@link Type}
   *                                   of {@code defaultValue} does not match {@code type}
   */
  public void setDefaultValue(Value defaultValue) throws IllegalValueTypeException {
    if (!defaultValue.getType().checksAgainst(this.type.get())) {
      throw new IllegalValueTypeException(defaultValue, this.type.get(), "Illegal Type:");
    }
    this.defaultValue.set(defaultValue);
  }
}
