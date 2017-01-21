package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.ObjectProperty;

import java.util.List;

/**
 * @author Benjamin Alt
 */
public class SpecificationTable<C, D> {

  private ObjectProperty<ColumnChangeInfo<C>> columnChange;
  private ObjectProperty<RowChangeInfo<C, D>> rowChange;
  private List<D> durations;

  public enum Change {
    ADD,
    REMOVE
  }

  public static class ColumnChangeInfo<C> {
    public final SpecificationColumn<C> column;
    public final String columnId;
    public final Change changeType;

    public ColumnChangeInfo(SpecificationColumn<C> column, String columnId, Change changeType) {
      this.column = column;
      this.columnId = columnId;
      this.changeType = changeType;
    }
  }

  public static class RowChangeInfo<C, D> {
    public final SpecificationRow<C, D> row;
    public final int rowNum;
    public final Change changeType;

    public RowChangeInfo(SpecificationRow<C, D> row, int rowNum, Change changeType) {
      this.row = row;
      this.rowNum = rowNum;
      this.changeType = changeType;
    }
  }

  public C getCell(int row, String column) {
    return null;
  }

  public SpecificationColumn<C> getColumn(String column) {
    return null;
  }

  public void addColumn(String columnId, SpecificationColumn<C> column) {

  }

  public void removeColumn(String columnId) {

  }

  public SpecificationRow<C, D> getRow(int row) {
    return null;
  }

  public void addRow(int rowNum, SpecificationRow<C, D> row) {

  }

  public void removeRow(int rowNum) {

  }

  public D getDuration(int rowNum) {
    return null;
  }

  public RowChangeInfo getRowChange() {
    return rowChange.get();
  }

  public ObjectProperty<RowChangeInfo<C, D>> rowChangeProperty() {
    return rowChange;
  }

  public void setRowChange(RowChangeInfo rowChange) {
    this.rowChange.set(rowChange);
  }

  public ColumnChangeInfo getColumnChange() {
    return columnChange.get();
  }

  public ObjectProperty<ColumnChangeInfo<C>> columnChangeProperty() {
    return columnChange;
  }

  public void setColumnChange(ColumnChangeInfo columnChange) {
    this.columnChange.set(columnChange);
  }
}
