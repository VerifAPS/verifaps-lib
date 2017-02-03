package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import org.apache.commons.lang3.builder.EqualsBuilder;

/**
 * Created by csicar on 11.01.17.
 */
public class SpecIoVariable extends IoVariable {
  private StringProperty name;
  private ObjectProperty<Type> type;
  private ObjectProperty<VariableCategory> category;

  /**
   * Creates a variable that appears in the specification.
   *
   * @param category The category of the variable
   * @param type     The type of the variable
   * @param name     The name of the Variable
   */
  public SpecIoVariable(VariableCategory category, Type type, String name) {
    this.category = new SimpleObjectProperty<>(category);
    this.type = new SimpleObjectProperty<>(type);
    this.name = new SimpleStringProperty(name);
  }

  public String getName() {
    return name.get();
  }

  public StringProperty nameProperty() {
    return name;
  }

  public void setName(String name) {
    this.name.set(name);
  }

  @Override
  public Type getType() {
    return type.get();
  }

  public ObjectProperty<Type> typeProperty() {
    return type;
  }

  public void setType(Type type) {
    this.type.set(type);
  }

  @Override
  public VariableCategory getCategory() {
    return category.get();
  }

  public ObjectProperty<VariableCategory> categoryProperty() {
    return category;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (!(o instanceof SpecIoVariable)) return false;

    SpecIoVariable that = (SpecIoVariable) o;

    if (name != null ? !name.get().equals(that.name.get()) : that.name != null) return false;
    if (type != null ? !type.get().equals(that.type.get()) : that.type != null) return false;
    return category != null ? category.get().equals(that.category.get()) : that.category == null;
  }

  @Override
  public int hashCode() {
    int result = name != null ? name.hashCode() : 0;
    result = 31 * result + (type != null ? type.hashCode() : 0);
    result = 31 * result + (category != null ? category.hashCode() : 0);
    return result;
  }

  public String toString() {
    return "SpecIoVariable(" + category.get() + " " + name.get() + " : " + type.get().getTypeName() + ")";
  }
}
