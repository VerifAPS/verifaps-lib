package edu.kit.iti.formal.stvs.model.common;

import java.util.Objects;
import java.util.Optional;

/**
 * Created by csicar on 10.01.17.
 */
public class Selection {

  private NullableProperty<String> column;
  private NullableProperty<Integer>  row;

  public Selection(String column, int row) {
    this.column = new NullableProperty<>(column);
    this.row = new NullableProperty<>(row);
  }

  public Selection(String column) {
    this.column = new NullableProperty<>(column);
    this.row = new NullableProperty<>();
  }

  public Selection(int row) {
    this.column = new NullableProperty<>();
    this.row = new NullableProperty<>(row);
  }

  public Selection() {
    this.column = new NullableProperty<>();
    this.row = new NullableProperty<>();
  }

  public Optional<String> getColumn() {
    return Optional.ofNullable(column.get());
  }

  public NullableProperty<String> columnProperty() {
    return column;
  }

  public void setColumn(String column) {
    this.column.set(column);
  }

  public Optional<Integer> getRow() {
    return Optional.ofNullable(row.get());
  }

  public NullableProperty<Integer> rowProperty() {
    return row;
  }

  public void setRow(int row) {
    this.row.set(row);
  }

  public void clear(){
    this.row.set(null);
    this.column.set(null);
  }


  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;

    Selection selection = (Selection) o;

    if (!column.get().equals(selection.column.get())) return false;
    return row.get().equals(selection.row.get());

  }

  @Override
  public int hashCode() {
    int result = Objects.hashCode(column.get());
    result = 31 * result + Objects.hashCode(row.get());
    return result;
  }
}
