package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
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
public class SpecificationTable<C, D> {

  // This is not an ObservableMap, because SpecIoVariable contains the columnHeader string
  // itself, so if it were an ObservableMap it would duplicate this information (and
  // one had to synchronize it, listen on the name property of SpecIoVariable, etc)
  protected ObservableList<SpecIoVariable> specIoVariables;
  protected ObservableList<SpecificationRow<C>> rows;
  protected ObservableList<D> durations;

  public SpecificationTable(Callback<D, Observable[]> durationExtractor) {
    this.rows = FXCollections.observableArrayList(specificationRow -> new Observable[] { specificationRow });
    this.durations = FXCollections.observableArrayList(durationExtractor);
    this.specIoVariables = FXCollections.observableArrayList();

    this.rows.addListener(this::onRowChange);
    this.specIoVariables.addListener(this::onSpecIoVariableChange);
    this.durations.addListener(this::onDurationChange);
  }

  public ObservableList<SpecificationRow<C>> getRows() {
    return rows;
  }

  public ObservableList<D> getDurations() {
    return durations;
  }

  public SpecificationColumn<C> getColumnByName(String specIoVarName) {
    SpecIoVariable specIoVariable = getSpecIoVariableByName(specIoVarName);
    List<C> cells = rows.stream()
        .map(row -> row.getCells().get(specIoVarName))
        .collect(Collectors.toList());
    return new SpecificationColumn<>(cells);
  }

  public SpecificationColumn<C> removeColumnByName(String specIoVarName) {
    SpecificationColumn<C> column = getColumnByName(specIoVarName);
    specIoVariables.remove(getSpecIoVariableByName(specIoVarName));
    for (SpecificationRow<C> row : rows) {
      row.getCells().remove(specIoVarName);
    }
    onColumnRemoved(column);
    return column;
  }

  public void addColumn(SpecIoVariable ioVariable, SpecificationColumn<C> column) {
    // throws IllegalArgumentException if a var with same name already exists:
    specIoVariables.add(ioVariable);

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
      rows.get(row).getCells().put(ioVariable.getName(), column.getCells().get(row));
    }
    onColumnAdded(column);
  }

  public Optional<SpecIoVariable> getOptionalSpecIoVariableByName(String specIoVarName) {
    return specIoVariables.stream()
        .filter(specIoVariable -> specIoVariable.getName().equals(specIoVarName))
        .findAny();
  }

  public SpecIoVariable getSpecIoVariableByName(String specIoVarName) {
    return getOptionalSpecIoVariableByName(specIoVarName)
        .orElseThrow(() ->
            new NoSuchElementException("Column does not exist: "
                + StringEscapeUtils.escapeJava(specIoVarName)));
  }

  /**
   * Get the SpecIoVariables for this table, i.e. the column headers.
   *
   * <p>You should <strong>not mutate</strong> this list. For adding new
   * columns, use addNewColumn</p>
   * @return the list of SpecIoVariables
   */
  public ObservableList<SpecIoVariable> getSpecIoVariables() {
    return this.specIoVariables;
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

  protected void onSpecIoVariableChange(ListChangeListener.Change<? extends SpecIoVariable> change) {
    while (change.next()) {
      if (change.wasAdded()) {
        onSpecIoVariableAdded(change.getAddedSubList());
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
      if (addedRow.getCells().size() != specIoVariables.size()) {
        throw new IllegalArgumentException("Illegal width for row "
            + StringEscapeUtils.escapeJava(addedRow.toString()) + ", expected width: "
            + specIoVariables.size());
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

  protected void onSpecIoVariableAdded(List<? extends SpecIoVariable> added) {
    for (SpecIoVariable specIoVariable : added) {
      String columnId = specIoVariable.getName();
      getOptionalSpecIoVariableByName(columnId)
          .ifPresent(otherVariableWithSameName -> {
            if (otherVariableWithSameName != specIoVariable) {
              throw new IllegalArgumentException(
                  "Cannot add SpecIoVariable that collides with another SpecIoVariable: "
                      + StringEscapeUtils.escapeJava(columnId));
            }
          });
    }
  }

  protected void onSpecIoVariableRemoved(List<? extends SpecIoVariable> removed) {
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
            append(getSpecIoVariables(), rhs.getSpecIoVariables()).
            append(getRows(), rhs.getRows()).
            append(getDurations(), rhs.getDurations()).
            isEquals();
  }
}
