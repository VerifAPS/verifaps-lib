package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;

import java.util.*;

/**
 * @author Benjamin Alt
 */
public class SpecificationTable<C, D> {

  private ObjectProperty<ColumnChangeInfo<C>> columnChange;
  private ObjectProperty<RowChangeInfo<C>> rowChange;
  protected Map<String, SpecificationColumn<C>> columns;
  protected ObjectProperty<Map<Integer,D>> durations;

  public SpecificationTable() {
    columnChange = new SimpleObjectProperty<>();
    rowChange = new SimpleObjectProperty<>();
    columns = new HashMap<>();
    durations = new SimpleObjectProperty<>(new HashMap<Integer,D>());
  }

  public SpecificationTable(Map<String, SpecificationColumn<C>> columns, Map<Integer,D> durations) {
    columnChange = new SimpleObjectProperty<>();
    rowChange = new SimpleObjectProperty<>();
    this.columns = columns;
    this.durations = new SimpleObjectProperty<>(new HashMap<>(durations));
  }

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

  public static class RowChangeInfo<C> {
    public final SpecificationRow<C> row;
    public final int rowNum;
    public final Change changeType;

    public RowChangeInfo(SpecificationRow<C> row, int rowNum, Change changeType) {
      this.row = row;
      this.rowNum = rowNum;
      this.changeType = changeType;
    }
  }

  public C getCell(int row, String columnId) {
    SpecificationColumn<C> specColumn = columns.get(columnId);
    if (specColumn == null) {
      throw new NoSuchElementException("No such table column: " + columnId);
    }
    return specColumn.getCellForRow(row);
  }

  public SpecificationColumn<C> getColumn(String columnId) {
    SpecificationColumn<C> specColumn = columns.get(columnId);
    if (specColumn == null) {
      throw new NoSuchElementException("No such table column: " + columnId);
    }
    return specColumn;
  }

  public void addColumn(String columnId, SpecificationColumn<C> column) {
    if (columns.containsKey(columnId)) {
      throw new IllegalArgumentException("A column with the name " + columnId + " already exists!");
    }
    columns.put(columnId, column);
    columnChange.set(new ColumnChangeInfo<C>(column, columnId, Change.ADD));
  }

  public void removeColumn(String columnId) {
    if (!columns.containsKey(columnId)) {
      throw new NoSuchElementException("No such table column: " + columnId);
    }
    SpecificationColumn<C> column = columns.remove(columnId);
    columnChange.set(new ColumnChangeInfo<C>(column, columnId, Change.REMOVE));
  }

  public SpecificationRow<C> getRow(int rowNum) {
    Map<String, C> cells = new HashMap<String, C>();
    for (String columnId : columns.keySet()) {
      cells.put(columnId, columns.get(columnId).getCellForRow(rowNum));
    }
    return new SpecificationRow<C>(cells);
  }

  public void addRow(int rowNum, SpecificationRow<C> row) {
    // Insert a cell into each column
    for (String columnId : columns.keySet()) {
      C newCell = row.getCellForVariable(columnId);
      if (newCell == null) {
        throw new NoSuchElementException("Cannot add row: IO variable " + columnId + " does not exist");
      }
      columns.get(columnId).insertCell(rowNum, newCell);
    }
    rowChange.setValue(new RowChangeInfo<C>(row, rowNum, Change.ADD));
  }

  /**
   * Convenience method to add a duration along with a row.
   * @param rowNum
   * @param row
   * @param duration
   */
  public void addRow(int rowNum, SpecificationRow<C> row, D duration) {
    addRow(rowNum, row);
    durations.get().put(rowNum, duration);
  }

  public void removeRow(int rowNum) {
    /* Remove the cell from each column */
    HashMap<String, C> removedCells = new HashMap<String, C>();
    for (String columnId : columns.keySet()) {
      SpecificationColumn<C> column = columns.get(columnId);
      C removedCell = column.removeCell(rowNum);
      removedCells.put(columnId, removedCell);
    }
    /* If there is a duration for that row, remove it as well */
    durations.get().remove(rowNum);
    rowChange.setValue(new RowChangeInfo<C>(new SpecificationRow<C>(removedCells), rowNum, Change.REMOVE));
  }

  public void setDuration(int rowNum, D duration) {
    durations.get().put(rowNum, duration);
  }

  public D getDuration(int rowNum) {
    return durations.get().get(rowNum);
  }

  public ObjectProperty<Map<Integer,D>> durationsProperty() {
    return durations;
  }

  public RowChangeInfo getRowChange() {
    return rowChange.get();
  }

  public ObjectProperty<RowChangeInfo<C>> rowChangeProperty() {
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
