package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.beans.Observable;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.util.Callback;
import org.apache.commons.lang3.builder.EqualsBuilder;

/**
 * Created by csicar on 10.01.17.
 */
public class FreeVariable implements Variable {

  public static final Callback<FreeVariable, Observable[]> EXTRACTOR =
      freeVar -> new Observable[] {
          freeVar.nameProperty(),
          freeVar.typeProperty(),
          freeVar.defaultValueProperty()
      };


  private final StringProperty name;
  private final StringProperty type;
  private final StringProperty defaultValue;

  /**
   * Creates a free variable with a name and type.
   * A default value will be generated through {@link Type#generateDefaultValue()}.
   *
   * @param name Name of the free variable
   * @param type Identifier of the type of the free variable
   */
  public FreeVariable(String name, String type) {
    this.name = new SimpleStringProperty(name);
    this.type = new SimpleStringProperty(type);
    this.defaultValue = new SimpleStringProperty("");
  }

  /**
   * Creates a free variable with a name, type and default value.
   *
   * @param name         Name of the free variable
   * @param type         Identifier of the type of the free variable
   * @param defaultValue Default value of the free variable
   */
  public FreeVariable(String name, String type, String defaultValue) {
    this.name = new SimpleStringProperty(name);
    this.type = new SimpleStringProperty(type);
    this.defaultValue = new SimpleStringProperty(defaultValue);
  }

  public String getName() {
    return name.get();
  }

  public StringProperty nameProperty() {
    return name;
  }

  public String getType() {
    return type.get();
  }

  public StringProperty typeProperty() {
    return type;
  }

  /**
   * Sets the type of this variable.
   * @param type identifier of the new type for the free variable
   */
  public void setType(String type) {
    this.type.set(type);
  }

  public String getDefaultValue() {
    return defaultValue.get();
  }

  public StringProperty defaultValueProperty() {
    return defaultValue;
  }

  /**
   * Assigns a new value to the free variable.
   */
  public void setDefaultValue(String defaultValue) {
    this.defaultValue.set(defaultValue);
  }

  @Override
  public String toString() {
    return "FreeVariable{"
        + "name=" + name.get()
        + ", type=" + type.get()
        + ", defaultValue=" + defaultValue.get()
        + '}';
  }

  @Override
  public boolean equals(Object obj) {
    if (!(obj instanceof FreeVariable)) return false;
    if (obj == this) return true;

    FreeVariable rhs = (FreeVariable) obj;
    return new EqualsBuilder().
            append(name.get(), rhs.name.get()).
            append(type.get(), rhs.type.get()).
            append(defaultValue.get(), rhs.defaultValue.get()).
            isEquals();
  }
}
