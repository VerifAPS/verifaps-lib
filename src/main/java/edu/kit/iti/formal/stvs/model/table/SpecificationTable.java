package edu.kit.iti.formal.stvs.model.table;

import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;

import java.util.*;

/**
 * @author Benjamin Alt
 */
public class SpecificationTable<C, D> {

  protected int height;
  protected ObservableList<SpecificationColumn<C>> columns;
  protected ObservableList<SpecificationRow<C>> rows;
  protected ObservableList<D> durations;

  public SpecificationTable() {
    this(new ArrayList<>(), new ArrayList<>());
  }

  public SpecificationTable(List<SpecificationColumn<C>> columns, List<D> durations) {
    this.columns = FXCollections.observableArrayList(columns);
    this.columns.addListener(this::onColumnChange);
    initHeight();
    this.rows = FXCollections.observableArrayList(makeRowList(columns));
    this.rows.addListener(this::onRowChange);
    this.durations = FXCollections.observableArrayList(durations);
  }

  protected void initHeight() {
    height = 0;
    for (SpecificationColumn<C> col : this.columns) {
      if (height == 0) height = col.getCells().size();
      if (height != col.getCells().size()) throw new IllegalArgumentException("Inconsistent " +
          "column heights: Not all columns have height " + height);
    }
  }

  public int getHeight() {
    return height;
  }

  public ObservableList<SpecificationColumn<C>> getColumns() {
    return columns;
  }

  public ObservableList<SpecificationRow<C>> getRows() {
    return rows;
  }

  public ObservableList<D> getDurations() {
    return durations;
  }

  protected void onColumnChange(ListChangeListener.Change<? extends SpecificationColumn<C>> change) {
    if (change.wasAdded()) {
      onColumnAdded(change.getAddedSubList());
    }
    if (change.wasRemoved()) {
      onColumnRemoved(change.getRemoved());
    }
  }

  protected void onRowChange(ListChangeListener.Change<? extends SpecificationRow<C>> change) {
    if (change.wasPermutated()) {
      onRowOrderChanged();
    }
    if (change.wasAdded()) {
      onRowAdded(change.getAddedSubList());
    }
    if (change.wasRemoved()) {
      onRowRemoved(change.getRemoved());
    }
  }

  /**
   * Add one or more cells to each row if one or more columns were added.
   * @param added
   */
  private void onColumnAdded(List<? extends SpecificationColumn<C>> added) {
    for (SpecificationColumn addedCol : added) {
      if (addedCol.getCells().size() != height) {
        throw new IllegalStateException("Illegal height for column " + addedCol.getSpecIoVariable
            ().getName());
      }
      for (SpecificationColumn<C> existingCol : columns) {
        if (addedCol.getSpecIoVariable().getName().equals(existingCol.getSpecIoVariable().getName
            ())) {
          throw new IllegalStateException("A column for variable " + addedCol.getSpecIoVariable()
              .getName() + " already exists");
        }
      }
    }
    for (SpecificationColumn<C> addedCol : added) {
      for (int i = 0; i < rows.size(); i++) {
        C addedCell = addedCol.getCells().get(i);
        rows.get(i).getCells().put(addedCol.getSpecIoVariable().getName(), addedCell);
      }
    }
  }

  /**
   * Remove the last cell(s) from each row if one or more columns were removed.
   * @param removed
   */
  private void onColumnRemoved(List<? extends SpecificationColumn<C>> removed) {
    for (SpecificationColumn<C> removedCol : removed) {
      for (int i = 0; i < rows.size(); i++) {
        C removedCell = removedCol.getCells().get(i);
        rows.get(i).getCells().remove(removedCol.getSpecIoVariable().getName(), removedCell);
      }
    }
  }

  /**
   * Add one or more cells to each column if one or more rows were added.
   * @param added
   */
  private void onRowAdded(List<? extends SpecificationRow<C>> added) {
    for (int i = 0; i < added.size(); i++) {
      if (added.get(i).getCells().size() != columns.size()) {
        throw new IllegalStateException("Illegal width for row " + i);
      }
    }
    for (SpecificationRow<C> addedRow : added) {
      for (SpecificationColumn<C> col : columns) {
        C addedCell = addedRow.getCells().get(col.getSpecIoVariable().getName());
        col.getCells().add(addedCell);
      }
    }
  }

  /**
   * Remove the last cell(s) from all columns if one or more rows were removed.
   */
  private void onRowRemoved(List<? extends SpecificationRow<C>> removed) {
    for (SpecificationRow<C> removedRow : removed) {
      for (SpecificationColumn<C> col : columns) {
        C removedCell = removedRow.getCells().get(col.getSpecIoVariable().getName());
        col.getCells().remove(removedCell);
      }
    }
  }

  /**
   * Adapt the order of the cells in a column if the order of the rows changed.
   */
  private void onRowOrderChanged() {
    for (SpecificationColumn<C> col : columns) {
      for (int i = 0; i < rows.size(); i++) {
        col.getCells().set(i, rows.get(i).getCells().get(col.getSpecIoVariable().getName()));
      }
    }
  }

  protected List<SpecificationRow<C>> makeRowList(List<SpecificationColumn<C>> columns) {
    List<SpecificationRow<C>> rowList = new ArrayList<>();
    for (int i = 0; i < height; i++) {
      Map<String, C> cellMap = new HashMap<String, C>();
      for (SpecificationColumn<C> col : this.columns) {
        cellMap.put(col.getSpecIoVariable().getName(), col.getCells().get(i));
      }
      rowList.add(new SpecificationRow<>(cellMap));
    }
    return rowList;
  }
}
