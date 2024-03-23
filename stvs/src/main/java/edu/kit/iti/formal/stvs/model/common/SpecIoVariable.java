package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.table.Commentable;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

/**
 * An input/output variable in a specification table.
 * @author Philipp
 */
public class SpecIoVariable extends IoVariable implements Commentable {

  private StringProperty name;
  private StringProperty type;
  private ObjectProperty<VariableCategory> category;
  private ObjectProperty<VariableRole> role;
  private ColumnConfig columnConfig;
  private StringProperty comment;


  /**
   * Creates a variable that appears in the specification.
   *
   * @param category The category of the variable
   * @param role The role the variable plays in Verification and Concretisation e.g. Assume / Assert
   * @param typeIdentifier The identifier of the type of the variable
   * @param name The name of the Variable
   */
  public SpecIoVariable(VariableCategory category, VariableRole role, String typeIdentifier, String name) {
    this.category = new SimpleObjectProperty<>(category);
    this.role = new SimpleObjectProperty<>(role);
    this.type = new SimpleStringProperty(typeIdentifier);
    this.name = new SimpleStringProperty(name);
    this.columnConfig = new ColumnConfig();
    this.comment = new SimpleStringProperty("");
  }

  /**
   * Creates a variable that appears in the specification.
   * role will be the standard role for the given category
   * @param category The category of the variable
   * @param typeIdentifier The identifier of the type of the variable
   * @param name The name of the Variable
   */
  public SpecIoVariable(VariableCategory category, String typeIdentifier, String name) {
    this(category, category.getDefaultRole(), typeIdentifier, name);
  }


  /**
   * Copy constructor: Create a deep copy of a given SpecIoVariable.
   * @param specIoVariable The SpecIoVariable to copy
   */
  public SpecIoVariable(SpecIoVariable specIoVariable) {
    this(specIoVariable.getCategory(), specIoVariable.getRole(), specIoVariable.getType(), specIoVariable.getName());
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
  public String getType() {
    return type.get();
  }

  public StringProperty typeProperty() {
    return type;
  }

  public void setType(String type) {
    this.type.set(type);
  }

  @Override
  public VariableCategory getCategory() {
    return category.get();
  }

  public void setCategory(VariableCategory category) {
    this.category.set(category);
  }

  public ObjectProperty<VariableCategory> categoryProperty() {
    return category;
  }

  @Override
  public String toString() {
    return "SpecIoVariable(" + category.get() + " " + name.get() + " : " + type.get() + ")";
  }

  public ColumnConfig getColumnConfig() {
    return columnConfig;
  }

  public void setColumnConfig(ColumnConfig columnConfig) {
    this.columnConfig = columnConfig;
  }

  @Override
  public void setComment(String comment) {
    this.comment.set(comment);
  }

  @Override
  public String getComment() {
    return this.comment.get();
  }

  @Override
  public StringProperty commentProperty() {
    return this.comment;
  }

  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null || getClass() != obj.getClass()) {
      return false;
    }

    SpecIoVariable that = (SpecIoVariable) obj;

    if (name != null ? !name.get().equals(that.name.get()) : that.name != null) {
      return false;
    }
    if (type != null ? !type.get().equals(that.type.get()) : that.type != null) {
      return false;
    }
    if (category != null ? !category.get().equals(that.category.get()) : that.category != null) {
      return false;
    }
    return columnConfig != null ? columnConfig.equals(that.columnConfig)
        : that.columnConfig == null;
  }

  @Override
  public int hashCode() {
    int result = name != null ? name.hashCode() : 0;
    result = 31 * result + (type != null ? type.hashCode() : 0);
    result = 31 * result + (category != null ? category.hashCode() : 0);
    result = 31 * result + (columnConfig != null ? columnConfig.hashCode() : 0);
    return result;
  }

  public VariableRole getRole() {
    return role.get();
  }

  public ObjectProperty<VariableRole> roleProperty() {
    return role;
  }
}
