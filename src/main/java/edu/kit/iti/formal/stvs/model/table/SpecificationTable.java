package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.Named;
import javafx.beans.Observable;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.util.Callback;
import org.apache.commons.lang3.StringEscapeUtils;
import org.apache.commons.lang3.builder.EqualsBuilder;

import java.util.List;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * @author Benjamin Alt
 * @author Philipp
 */
public class SpecificationTable<H extends Named, C, D> {

  protected ObservableList<H> columnHeaders;
  protected ObservableList<SpecificationRow<C>> rows;
  protected ObservableList<D> durations;

  public SpecificationTable(Callback<D, Observable[]> durationExtractor) {
    this.rows = FXCollections.observableArrayList(specificationRow -> new Observable[] { specificationRow });
    this.durations = FXCollections.observableArrayList(durationExtractor);
    this.columnHeaders = FXCollections.observableArrayList();

    this.rows.addListener(this::onRowChange);
    this.columnHeaders.addListener(this::onColumnHeadersChanged);
    this.durations.addListener(this::onDurationChange);
  }

  public ObservableList<SpecificationRow<C>> getRows() {
    return rows;
  }

  public ObservableList<D> getDurations() {
    return durations;
  }

  public SpecificationColumn<C> getColumnByName(String columnHeaderName) {
    // ensure there is a column header with this name
    H columnHeader = getColumnHeaderByName(columnHeaderName);
    List<C> cells = rows.stream()
        .map(row -> row.getCells().get(columnHeader.getName()))
        .collect(Collectors.toList());
    return new SpecificationColumn<>(cells);
  }

  public SpecificationColumn<C> removeColumnByName(String specIoVarName) {
    SpecificationColumn<C> column = getColumnByName(specIoVarName);
    columnHeaders.remove(getColumnHeaderByName(specIoVarName));
    for (SpecificationRow<C> row : rows) {
      row.getCells().remove(specIoVarName);
    }
    onColumnRemoved(column);
    return column;
  }

  public void addColumn(H columnHeader, SpecificationColumn<C> column) {
    // throws IllegalArgumentException if a var with same name already exists:
    columnHeaders.add(columnHeader);

    if (rows.size() == 0) {
      throw new IllegalStateException("Cannot add columns to empty table, add rows first "
          + "(maybe fill table by rows, instead of by columns)");
    }

    // Check correctness of added column
    int colHeight = column.getCells().size();
    if (colHeight != rows.size()) {
      throw new IllegalArgumentException(
          "Cannot add column with incorrect height " + colHeight + ", expected: " + rows.size());
    }
    for (int row = 0; row < rows.size(); row++) {
      // This fixes a bug, where there is an inconsistent state in the listener for changes in rows,
      // since it is possible, that listeners on rows are invoked even though this loop is not done.
      // One might want to have something like adding a cell to each row 'simultaneously'
      rows.get(row).putWithoutListenersNotice(columnHeader.getName(), column.getCells().get(row));
    }
    rows.get(0).invokeListeners();
    onColumnAdded(column);
  }

  public Optional<H> getOptionalSpecIoVariableByName(String columnHeaderName) {
    return columnHeaders.stream()
        .filter(specIoVariable -> specIoVariable.getName().equals(columnHeaderName))
        .findAny();
  }

  public H getColumnHeaderByName(String columnHeaderName) {
    return getOptionalSpecIoVariableByName(columnHeaderName)
        .orElseThrow(() ->
            new NoSuchElementException("Column does not exist: "
                + StringEscapeUtils.escapeJava(columnHeaderName)));
  }

  /**
   * Get the SpecIoVariables for this table, i.e. the column headers.
   *
   * <p>You should <strong>not mutate</strong> this list. For adding new
   * columns, use addNewColumn</p>
   * @return the list of SpecIoVariables
   */
  public ObservableList<H> getColumnHeaders() {
    return this.columnHeaders;
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

  protected void onColumnHeadersChanged(ListChangeListener.Change<? extends H> change) {
    while (change.next()) {
      if (change.wasAdded()) {
        onColumnHeaderAdded(change.getAddedSubList());
      }
      if (change.wasRemoved()) {
        onSpecIoVariableRemoved(change.getRemoved());
      }
    }
  }

  protected void onDurationChange(ListChangeListener.Change<? extends D> change) {
    while (change.next()) {
      if (change.wasAdded()) {
        onDurationAdded(change.getAddedSubList());
      }
      if (change.wasRemoved()) {
        onDurationRemoved(change.getRemoved());
      }
    }
  }

  protected void onRowAdded(List<? extends SpecificationRow<C>> added) {
    for (SpecificationRow<C> addedRow : added) {
      // Check correctness of added row
      if (addedRow.getCells().size() != columnHeaders.size()) {
        throw new IllegalArgumentException("Illegal width for row "
            + StringEscapeUtils.escapeJava(addedRow.toString()) + ", expected width: "
            + columnHeaders.size());
      }
      if (!addedRow.getCells().keySet().stream().allMatch(columnId ->
              getOptionalSpecIoVariableByName(columnId).isPresent())) {
        throw new IllegalArgumentException("Added row contains unknown IoVariable: "
            + StringEscapeUtils.escapeJava(addedRow.toString()));
      }
    }
  }

  protected void onRowRemoved(List<? extends SpecificationRow<C>> removed) {
  }

  protected void onRowOrderChanged() {
  }

  protected void onColumnAdded(SpecificationColumn<C> column) {
  }

  protected void onColumnRemoved(SpecificationColumn<C> column) {
  }

  protected void onColumnHeaderAdded(List<? extends H> added) {
    for (H columnHeader : added) {
      String columnId = columnHeader.getName();
      getOptionalSpecIoVariableByName(columnId)
          .ifPresent(otherVariableWithSameName -> {
            if (otherVariableWithSameName != columnHeader) {
              throw new IllegalArgumentException(
                  "Cannot add SpecIoVariable that collides with another SpecIoVariable: "
                      + StringEscapeUtils.escapeJava(columnId));
            }
          });
    }
  }

  protected void onSpecIoVariableRemoved(List<? extends H> removed) {
  }

  protected void onDurationAdded(List<? extends D> added) {
  }

  protected void onDurationRemoved(List<? extends D> removed) {
  }

  @Override
  public boolean equals(Object obj) {
    if (!(obj instanceof SpecificationTable))
      return false;
    if (obj == this)
      return true;

    SpecificationTable rhs = (SpecificationTable) obj;
    return new EqualsBuilder().
            append(getColumnHeaders(), rhs.getColumnHeaders()).
            append(getRows(), rhs.getRows()).
            append(getDurations(), rhs.getDurations()).
            isEquals();
  }

}
