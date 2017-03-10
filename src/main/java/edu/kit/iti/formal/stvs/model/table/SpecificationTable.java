package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.Named;

import java.util.List;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.stream.Collectors;

import javafx.beans.Observable;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.util.Callback;
import org.apache.commons.lang3.StringEscapeUtils;

/**
 * A specification table.
 *
 * @param <H> The column header type
 * @param <C> The cell type
 * @param <D> The duration type
 *
 * @author Benjamin Alt
 * @author Philipp
 */
public class SpecificationTable<H extends Named, C, D> {

  protected final static String DEFAULT_NAME = "Unnamed Specification";

  protected ObservableList<H> columnHeaders;
  protected ObservableList<SpecificationRow<C>> rows;
  protected ObservableList<D> durations;
  private StringProperty name;

  /**
   * Construct a new SpecificationTable with a default name, no rows or columns and the specified
   * column header and row extractors. These are needed for "deep observing" and are used to
   * indicate to observable collections such as {@link ObservableList} which properties of the
   * items in the collection should cause change events on the collection itself.
   * See also
   * <a href="http://stackoverflow.com/questions/31687642/callback-and-extractors-for-javafx-observablelist">this post</a>
   * on why and how extractors are used.
   * @param columnHeaderExtractor The extractor for the column headers
   * @param durationExtractor The extractor for the duration headers
   */
  public SpecificationTable(Callback<H, Observable[]> columnHeaderExtractor,
      Callback<D, Observable[]> durationExtractor) {
    this(DEFAULT_NAME, columnHeaderExtractor, durationExtractor);
  }

  /**
   * Construct a new SpecificationTable with a given name, no rows or columns and the specified
   * column header and row extractors. These are needed for "deep observing" and are used to
   * indicate to observable collections such as {@link ObservableList} which properties of the
   * items in the collection should cause change events on the collection itself.
   * See also
   * <a href="http://stackoverflow.com/questions/31687642/callback-and-extractors-for-javafx-observablelist">
   *   this post</a> on why and how extractors are used.
   * @param columnHeaderExtractor The extractor for the column headers
   * @param durationExtractor The extractor for the duration headers
   */
  public SpecificationTable(String name, Callback<H, Observable[]> columnHeaderExtractor,
      Callback<D, Observable[]> durationExtractor) {
    this.name = new SimpleStringProperty(name);
    this.rows =
        FXCollections.observableArrayList(specificationRow -> new Observable[] {specificationRow});
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

  /**
   * Return the column whose header has the given name.
   * @param columnHeaderName The name of the column header
   * @return The corresponding column
   * @throws NoSuchElementException if the column header does not exist
   */
  public SpecificationColumn<C> getColumnByName(String columnHeaderName) {
    H columnHeader = getColumnHeaderByName(columnHeaderName);
    List<C> cells = rows.stream().map(row -> row.getCells().get(columnHeader.getName()))
        .collect(Collectors.toList());
    return new SpecificationColumn<>(cells);
  }

  /**
   * Remove and return the column whose header has the given name.
   * @param columnHeaderName The name of the column header
   * @return The corresponding column (which was deleted from the table)
   * @throws NoSuchElementException if the column header does not exist
   */
  public SpecificationColumn<C> removeColumnByName(String columnHeaderName) {
    SpecificationColumn<C> column = getColumnByName(columnHeaderName);
    columnHeaders.remove(getColumnHeaderByName(columnHeaderName));
    for (SpecificationRow<C> row : rows) {
      row.getCells().remove(columnHeaderName);
    }
    onColumnRemoved(column);
    return column;
  }

  /**
   * Add a column with a given column header to the specification table.
   * @param columnHeader The column header for the column to be added
   * @param column The column to add
   * @throws IllegalArgumentException if the column header already exists in the specification table
   * @throws IllegalStateException if the table does not have any rows yet. First fill a table by
   *                               rows, then add columns if necessary/desired.
   * @throws IllegalArgumentException if the column height does not correspond to the number of
   *                                  rows already in the table.
   */
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

  /**
   * Get the column header with a given name.
   * @param columnHeaderName The name of the column header
   * @return An {@link Optional} containing the corresponding column header or an
   *         empty {@link Optional} there is no such header
   */
  public Optional<H> getOptionalColumnHeaderByName(String columnHeaderName) {
    return columnHeaders.stream()
        .filter(specIoVariable -> specIoVariable.getName().equals(columnHeaderName)).findAny();
  }

  /**
   * Get the column header with a given name.
   * @param columnHeaderName The name of the column header
   * @return The corresponding column header
   * @throws NoSuchElementException if there is no such column header
   */
  public H getColumnHeaderByName(String columnHeaderName) {
    return getOptionalColumnHeaderByName(columnHeaderName)
        .orElseThrow(() -> new NoSuchElementException(
            "Column does not exist: " + StringEscapeUtils.escapeJava(columnHeaderName)));
  }

  /**
   * Get the SpecIoVariables for this table, i.e. the column headers.
   * <p>
   * <p>
   * You should <strong>not mutate</strong> this list. For adding new columns, use
   * {@link SpecificationTable#addColumn(Named, SpecificationColumn)}.
   * </p>
   *
   * @return the list of SpecIoVariables
   */
  public ObservableList<H> getColumnHeaders() {
    return this.columnHeaders;
  }

  /**
   * Invoked when the list of row changes.
   * @param change The {@link javafx.collections.ListChangeListener.Change} object corresponding
   *               to the list change
   */
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
   * Invoked when the list of column headers changes.
   * @param change The {@link javafx.collections.ListChangeListener.Change} object corresponding
   *               to the list change
   */
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

  /**
   * Invoked when the list of durations changes.
   * @param change The {@link javafx.collections.ListChangeListener.Change} object corresponding
   *               to the list change
   */
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
        throw new IllegalArgumentException(
            "Illegal width for row " + StringEscapeUtils.escapeJava(addedRow.toString())
                + ", expected width: " + columnHeaders.size());
      }
      if (!addedRow.getCells().keySet().stream()
          .allMatch(columnId -> getOptionalColumnHeaderByName(columnId).isPresent())) {
        throw new IllegalArgumentException("Added row contains unknown IoVariable: "
            + StringEscapeUtils.escapeJava(addedRow.toString()));
      }
    }
  }

  protected void onRowRemoved(List<? extends SpecificationRow<C>> removed) {}

  protected void onRowOrderChanged() {}

  protected void onColumnAdded(SpecificationColumn<C> column) {}

  protected void onColumnRemoved(SpecificationColumn<C> column) {}

  protected void onColumnHeaderAdded(List<? extends H> added) {
    for (H columnHeader : added) {
      String columnId = columnHeader.getName();
      getOptionalColumnHeaderByName(columnId).ifPresent(otherVariableWithSameName -> {
        if (otherVariableWithSameName != columnHeader) {
          throw new IllegalArgumentException(
              "Cannot add SpecIoVariable that collides with another SpecIoVariable: "
                  + StringEscapeUtils.escapeJava(columnId));
        }
      });
    }
  }

  protected void onColumnHeaderRemoved(List<? extends H> removed) {}

  protected void onDurationAdded(List<? extends D> added) {}

  protected void onDurationRemoved(List<? extends D> removed) {}

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }

    SpecificationTable<?, ?, ?> that = (SpecificationTable<?, ?, ?>) o;

    if (getColumnHeaders() != null ? !getColumnHeaders().equals(that.getColumnHeaders())
        : that.getColumnHeaders() != null) {
      return false;
    }
    if (getRows() != null ? !getRows().equals(that.getRows()) : that.getRows() != null) {
      return false;
    }
    if (getDurations() != null ? !getDurations().equals(that.getDurations())
        : that.getDurations() != null) {
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

  @Override
  public String toString() {
    StringBuilder str = new StringBuilder(getClass().getSimpleName());
    str.append("\nDurations: ");
    getDurations().stream().map(Object::toString).forEach(string -> {
      str.append(string);
      str.append(',');
    });
    str.append("\nColumns: ");
    getColumnHeaders().stream().map(Object::toString).forEach(string -> {
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
