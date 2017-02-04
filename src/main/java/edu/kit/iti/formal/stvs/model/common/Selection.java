package edu.kit.iti.formal.stvs.model.common;

import javafx.beans.InvalidationListener;
import javafx.beans.Observable;
import javafx.beans.property.IntegerProperty;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

/**
 * Created by csicar on 10.01.17.
 */
public class Selection {

  private OptionalPropertyBase<String, StringProperty> column;
  private OptionalPropertyBase<Number, IntegerProperty> row;

  public Selection(String column, int row) {
    this.column = new OptionalPropertyBase<>(new SimpleStringProperty(column));
    this.row = new OptionalPropertyBase<>(new SimpleIntegerProperty(row));
  }

  public Selection(String column) {
    this.column = new OptionalPropertyBase<>(new SimpleStringProperty(column));
    this.row = OptionalPropertyBase.ofNull(new SimpleIntegerProperty());
  }

  public Selection(int row) {
    this.column = OptionalPropertyBase.ofNull(new SimpleStringProperty());
    this.row = new OptionalPropertyBase<>(new SimpleIntegerProperty(row));
  }

  public Selection() {
    this.column = OptionalPropertyBase.ofNull(new SimpleStringProperty());
    this.row = OptionalPropertyBase.ofNull(new SimpleIntegerProperty());
  }

  public String getColumn() {
    return column.get();
  }

  public OptionalPropertyBase<String, StringProperty> columnProperty() {
    return column;
  }

  public void setColumn(String column) {
    this.column.set(column);
  }

  public int getRow() {
    return row.get().intValue();
  }

  public OptionalPropertyBase<Number, IntegerProperty> rowProperty() {
    return row;
  }

  public void setRow(int row) {
    this.row.set(row);
  }
}
