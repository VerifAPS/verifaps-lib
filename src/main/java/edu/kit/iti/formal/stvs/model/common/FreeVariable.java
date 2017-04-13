package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.beans.Observable;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.util.Callback;

/**
 * A free variable. Free variables have a name, a type and a default value and can occur in
 * constraint expressions.
 * @author Philipp
 */
public class FreeVariable implements Variable {

  /**
   * The default extractor to allow observable collections containing FreeVariables to fire
   * change events when the properties of a FreeVariable change.
   */
  public static final Callback<FreeVariable, Observable[]> EXTRACTOR = freeVar -> new Observable[] {
      freeVar.nameProperty(), freeVar.typeProperty(), freeVar.constraintProperty()};
  private static final String DONTCARE = "-";

  private final StringProperty name;
  private final StringProperty type;
  private final StringProperty constraint;

  /**
   * Creates a free variable with a name and type. A default value will be generated through
   * {@link Type#generateDefaultValue()}.
   *
   * @param name Name of the free variable
   * @param type Identifier of the type of the free variable
   */
  public FreeVariable(String name, String type) {
    this(name, type, null);
  }

  /**
   * Creates a free variable with a name, type and default value.
   *
   * @param name Name of the free variable
   * @param type Identifier of the type of the free variable
   * @param constraint Default value of the free variable
   */
  public FreeVariable(String name, String type, String constraint) {
    this.name = new SimpleStringProperty(name);
    this.type = new SimpleStringProperty(type);
    this.constraint = new SimpleStringProperty(
            constraint == null ? DONTCARE : constraint);
  }

  /**
   * Copy constructor: Makes a deep copy of a given free variable.
   * @param freeVar The variable to copy
   */
  public FreeVariable(FreeVariable freeVar) {
    this(freeVar.getName(), freeVar.getType(), freeVar.getConstraint());
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
   *
   * @param type identifier of the new type for the free variable
   */
  public void setType(String type) {
    this.type.set(type);
  }

  public String getConstraint() {
    return constraint.get();
  }

  public StringProperty constraintProperty() {
    return constraint;
  }

  /**
   * Assigns a new value to the free variable.
   * @param constraint value to set to
   */
  public void setConstraint(String constraint) {
    this.constraint.set(constraint);
  }

  @Override
  public String toString() {
    return "FreeVariable{" + "name=" + name.get() + ", type=" + type.get() + ", constraint="
        + constraint.get() + '}';
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null || getClass() != obj.getClass()) {
      return false;
    }

    FreeVariable that = (FreeVariable) obj;

    if (getName() != null ? !getName().equals(that.getName()) : that.getName() != null) {
      return false;
    }
    if (getType() != null ? !getType().equals(that.getType()) : that.getType() != null) {
      return false;
    }
    return getConstraint() != null ? getConstraint().equals(that.getConstraint())
        : that.getConstraint() == null;
  }

  @Override
  public int hashCode() {
    int result = getName() != null ? getName().hashCode() : 0;
    result = 31 * result + (getType() != null ? getType().hashCode() : 0);
    result = 31 * result + (getConstraint() != null ? getConstraint().hashCode() : 0);
    return result;
  }
}
