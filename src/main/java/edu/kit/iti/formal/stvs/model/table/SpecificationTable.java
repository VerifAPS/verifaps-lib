package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;

import java.util.*;

/**
 * @author Benjamin Alt
 */
public class SpecificationTable<C, D> {

  private ObjectProperty<ColumnChangeInfo<C>> columnChange;
  private ObjectProperty<RowChangeInfo<C>> rowChange;
  private int height;
  protected Map<String, SpecificationColumn<C>> columns;
  protected ObservableList<D> durations;

  public SpecificationTable() {
    this(new HashMap<>(), new ArrayList<>());
  }

  public SpecificationTable(Map<String, SpecificationColumn<C>> columns, List<D> durations) {
    columnChange = new SimpleObjectProperty<>();
    rowChange = new SimpleObjectProperty<>();
    this.columns = columns;
    height = -1;
    for (SpecificationColumn<C> col : this.columns.values()) {
      if (height == -1) height = col.getNumberOfCells();
      if (height != col.getNumberOfCells()) throw new IllegalArgumentException("Inconsistent " +
          "column heights: Not all columns have height " + height);
    }
    this.durations = FXCollections.observableArrayList(durations);
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

  public int getHeight() {
    return height;
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
    } else if (column.getNumberOfCells() != height) {
      throw new IllegalArgumentException("Column does not have height " + height);
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
    height += 1;
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
    durations.add(rowNum, duration);
    height += 1;
  }

  /**
   * NB: Does not remove a possible duration for that row
   * @param rowNum
   */
  public void removeRow(int rowNum) {
    /* Remove the cell from each column */
    HashMap<String, C> removedCells = new HashMap<>();
    for (String columnId : columns.keySet()) {
      SpecificationColumn<C> column = columns.get(columnId);
      C removedCell = column.removeCell(rowNum);
      removedCells.put(columnId, removedCell);
    }
    rowChange.setValue(new RowChangeInfo<C>(new SpecificationRow<C>(removedCells), rowNum, Change.REMOVE));
    height -= 1;
  }

  public ObservableList<D> getDurations() {
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
