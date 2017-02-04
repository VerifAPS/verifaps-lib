package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;

import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

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
      if (height == 0) {
        height = col.getCells().size();
      }
      if (height != col.getCells().size()) {
        throw new IllegalArgumentException("Inconsistent "
            + "column heights: Not all columns have height " + height);
      }
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

  public SpecificationColumn<C> getColumnByName(String specIoVarName) {
    return columns.stream()
        .filter(column -> column.getSpecIoVariable().getName().equals(specIoVarName))
        .findFirst()
        .orElseThrow(() ->
            new NoSuchElementException("Column with name \"" + specIoVarName + "\" can't be found."));
  }

  public SpecificationColumn<C> removeColumnByName(String specIoVarName) {
    SpecificationColumn<C> column = getColumnByName(specIoVarName);
    getColumns().remove(column);
    return column;
  }

  public List<SpecIoVariable> getSpecIoVariables() {
    return columns.stream().map(SpecificationColumn::getSpecIoVariable).collect(Collectors.toList());
  }

  protected void onColumnChange(ListChangeListener.Change<? extends SpecificationColumn<C>> change) {
    while (change.next()) {
      if (change.wasAdded()) {
        onColumnAdded(change.getAddedSubList());
      }
      if (change.wasRemoved()) {
        onColumnRemoved(change.getRemoved());
      }
    }
  }

  protected void onRowChange(ListChangeListener.Change<? extends SpecificationRow<C>> change) {
    while (change.next()) {
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
  }

  /**
   * Add one or more cells to each row if one or more columns were added.
   * @param added
   */
  protected void onColumnAdded(List<? extends SpecificationColumn<C>> added) {
    for (SpecificationColumn addedCol : added) {
      if (addedCol.getCells().size() != height) {
        throw new IllegalArgumentException("Illegal height for column " + addedCol.getSpecIoVariable
            ().getName());
      }
      // The column is already added, so we have to test that it is duplicated
      if (columnPredicatePresentAtLeastTwice(
          column -> column.getSpecIoVariable().getName().equals(addedCol.getSpecIoVariable().getName()))) {
        throw new IllegalArgumentException("A column for variable " + addedCol.getSpecIoVariable()
            .getName() + " already exists");
      }
    }
    for (SpecificationColumn<C> addedCol : added) {
      for (int i = 0; i < rows.size(); i++) {
        C addedCell = addedCol.getCells().get(i);
        rows.get(i).getCells().put(addedCol.getSpecIoVariable().getName(), addedCell);
      }
    }
  }

  private boolean columnPredicatePresentAtLeastTwice(Predicate<SpecificationColumn<C>> columnPredicate) {
    return columns.stream().filter(columnPredicate).count() >= 2;
  }

  /**
   * Remove the last cell(s) from each row if one or more columns were removed.
   * @param removed
   */
  protected void onColumnRemoved(List<? extends SpecificationColumn<C>> removed) {
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
  protected void onRowAdded(List<? extends SpecificationRow<C>> added) {
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
  protected void onRowRemoved(List<? extends SpecificationRow<C>> removed) {
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
