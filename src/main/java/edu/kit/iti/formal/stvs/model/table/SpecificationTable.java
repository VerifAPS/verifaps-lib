package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;

import java.util.*;

/**
 * @author Benjamin Alt
 */
public class SpecificationTable<C, D> {

  private ObjectProperty<ColumnChangeInfo<C>> columnChange;
  private ObjectProperty<RowChangeInfo<C, D>> rowChange;
  protected Map<String, SpecificationColumn<C>> columns;
  protected ArrayList<D> durations;

  public SpecificationTable() {
    columnChange = new SimpleObjectProperty<>();
    rowChange = new SimpleObjectProperty<>();
    columns = new HashMap<>();
    durations = new ArrayList<>();
  }

  public SpecificationTable(Map<String, SpecificationColumn<C>> columns, List<D> durations) {
    columnChange = new SimpleObjectProperty<>();
    rowChange = new SimpleObjectProperty<>();
    // TODO: Make sure that the "height" of each column is the same as durations.size()
    for (SpecificationColumn<C> col : columns.values()) {
      if (col.getCells().size() != durations.size()) {
        throw new IllegalArgumentException("The height of each column must be identical to" +
            "the number of durations");
      }
    }
    this.columns = columns;
    this.durations = new ArrayList(durations);
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
    //TODO: Throw error if column already exists?
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

  public SpecificationRow<C, D> getRow(int rowNum) {
    Map<String, C> cells = new HashMap<String, C>();
    for (String columnId : columns.keySet()) {
      cells.put(columnId, columns.get(columnId).getCellForRow(rowNum));
    }
    D duration = durations.get(rowNum);
    return new SpecificationRow<C, D>(duration, cells);
  }

  public void addRow(int rowNum, SpecificationRow<C, D> row) {
    // Insert a cell into each column
    for (String columnId : columns.keySet()) {
      C newCell = row.getCellForVariable(columnId);
      if (newCell == null) {
        throw new NoSuchElementException("Cannot add row: IO variable " + columnId + " does not exist");
      }
      columns.get(columnId).insertCell(rowNum, newCell);
    }
    durations.add(rowNum, row.getDuration());
    rowChange.setValue(new RowChangeInfo<C, D>(row, rowNum, Change.ADD));
  }

  public void removeRow(int rowNum) {
    // Remove the cell from each column
    HashMap<String, C> removedCells = new HashMap<String, C>();
    for (String columnId : columns.keySet()) {
      SpecificationColumn<C> column = columns.get(columnId);
      C removedCell = column.removeCell(rowNum);
      removedCells.put(columnId, removedCell);
    }
    D duration = durations.remove(rowNum);
    rowChange.setValue(new RowChangeInfo<C, D>(new SpecificationRow<C, D>(duration, removedCells), rowNum, Change.REMOVE));
  }

  public D getDuration(int rowNum) {
    return durations.get(rowNum);
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
