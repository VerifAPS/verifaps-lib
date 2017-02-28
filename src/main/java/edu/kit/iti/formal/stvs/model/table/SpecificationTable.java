package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.Named;
import javafx.beans.Observable;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.util.Callback;
import org.apache.commons.lang3.StringEscapeUtils;

import java.util.List;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * @author Benjamin Alt
 * @author Philipp
 */
public class SpecificationTable<H extends Named, C, D> {

  protected final static String DEFAULT_NAME = "Unnamed Specification";

  protected ObservableList<H> columnHeaders;
  protected ObservableList<SpecificationRow<C>> rows;
  protected ObservableList<D> durations;
  private StringProperty name;

  public SpecificationTable(
      Callback<H, Observable[]> columnHeaderExtractor,
      Callback<D, Observable[]> durationExtractor) {
    this(DEFAULT_NAME, columnHeaderExtractor, durationExtractor);
  }

  public SpecificationTable(
      String name,
      Callback<H, Observable[]> columnHeaderExtractor,
      Callback<D, Observable[]> durationExtractor) {
    this.name = new SimpleStringProperty(name);
    this.rows = FXCollections.observableArrayList(
        specificationRow -> new Observable[] {specificationRow});
    this.durations = FXCollections.observableArrayList(durationExtractor);
    this.columnHeaders = FXCollections.observableArrayList(columnHeaderExtractor);

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
      rows.get(row).getCells().put(columnHeader.getName(), column.getCells().get(row));
    }
    onColumnAdded(column);
  }

  public Optional<H> getOptionalColumnHeaderByName(String columnHeaderName) {
    return columnHeaders.stream()
        .filter(specIoVariable -> specIoVariable.getName().equals(columnHeaderName))
        .findAny();
  }

  public H getColumnHeaderByName(String columnHeaderName) {
    return getOptionalColumnHeaderByName(columnHeaderName)
        .orElseThrow(() ->
            new NoSuchElementException("Column does not exist: "
                + StringEscapeUtils.escapeJava(columnHeaderName)));
  }

  /**
   * Get the SpecIoVariables for this table, i.e. the column headers.
   * <p>
   * <p>You should <strong>not mutate</strong> this list. For adding new
   * columns, use addNewColumn</p>
   *
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
        onColumnHeaderRemoved(change.getRemoved());
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
          getOptionalColumnHeaderByName(columnId).isPresent())) {
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
      getOptionalColumnHeaderByName(columnId)
          .ifPresent(otherVariableWithSameName -> {
            if (otherVariableWithSameName != columnHeader) {
              throw new IllegalArgumentException(
                  "Cannot add SpecIoVariable that collides with another SpecIoVariable: "
                      + StringEscapeUtils.escapeJava(columnId));
            }
          });
    }
  }

  protected void onColumnHeaderRemoved(List<? extends H> removed) {
  }

  protected void onDurationAdded(List<? extends D> added) {
  }

  protected void onDurationRemoved(List<? extends D> removed) {
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }

    SpecificationTable<?, ?, ?> that = (SpecificationTable<?, ?, ?>) o;

    if (getColumnHeaders() != null ? !getColumnHeaders().equals(that.getColumnHeaders()) : that.getColumnHeaders() != null) {
      return false;
    }
    if (getRows() != null ? !getRows().equals(that.getRows()) : that.getRows() != null) {
      return false;
    }
    if (getDurations() != null ? !getDurations().equals(that.getDurations()) : that.getDurations() != null) {
      return false;
    }
    return getName() != null ? getName().equals(that.getName()) : that.getName() == null;
  }

  @Override
  public int hashCode() {
    int result = getColumnHeaders() != null ? getColumnHeaders().hashCode() : 0;
    result = 31 * result + (getRows() != null ? getRows().hashCode() : 0);
    result = 31 * result + (getDurations() != null ? getDurations().hashCode() : 0);
    result = 31 * result + (getName() != null ? getName().hashCode() : 0);
    return result;
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

  public String toString() {
    StringBuilder str = new StringBuilder(getClass().getSimpleName());
    str.append("\nDurations: ");
    getDurations().stream().map(Object::toString)
        .forEach(string -> {
          str.append(string);
          str.append(',');
        });
    str.append("\nColumns: ");
    getColumnHeaders().stream().map(Object::toString)
        .forEach(string -> {
          str.append(string);
          str.append(',');
        });
    str.append("\nRows:\n");
    getRows().stream().forEachOrdered(row -> {
      getColumnHeaders().forEach(header -> {
        str.append(row.getCells().get(header.getName()));
        str.append(',');
      });
      str.append('\n');
    });
    return str.toString();
  }
}
