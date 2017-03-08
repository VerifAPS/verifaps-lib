package edu.kit.iti.formal.stvs.model.common;

import java.util.Objects;
import java.util.Optional;

/**
 * This class is used to represent a selected area in a specification table (a col,row-Tuple for a
 * cell, a column, or a row). It is generated (and used) when the user hovers over an area in the
 * timing diagram and represents the corresponding area in the table.
 *
 * @author Leon Kaucher
 */
public class Selection {

  private NullableProperty<String> column;
  private NullableProperty<Integer> row;
  private SelectionClickListener clickListener = (s, i) -> {
  };

  /**
   * Create a new Selection for a given column and row.
   * @param column The selected column
   * @param row The selected row
   */
  public Selection(String column, int row) {
    this.column = new NullableProperty<>(column);
    this.row = new NullableProperty<>(row);
  }

  /**
   * Create a new Selection for a given column.
   * @param column The selected column
   */
  public Selection(String column) {
    this.column = new NullableProperty<>(column);
    this.row = new NullableProperty<>();
  }

  /**
   * Create a new Selection for a given row.
   * @param row The selected row
   */
  public Selection(int row) {
    this.column = new NullableProperty<>();
    this.row = new NullableProperty<>(row);
  }

  /**
   * Create a new empty selection ("nothing was selected").
   */
  public Selection() {
    this.column = new NullableProperty<>();
    this.row = new NullableProperty<>();
  }

  /**
   * Specify a listener which is invoked when the user clicks on the selection in the timing
   * diagram. This can be used to trigger changes in the table etc.
   * @param listener The listener to be invoked when the timing diagram is clicked
   */
  public void setOnTimingDiagramSelectionClickListener(SelectionClickListener listener) {
    this.clickListener = listener;
  }

  /**
   * Fire a click event on a given column and row. This invokes the listener specified in
   * {@link Selection#setOnTimingDiagramSelectionClickListener(SelectionClickListener)}.
   * @param column The column which was clicked
   * @param row The row which was clicked
   */
  public void fireClickEvent(String column, int row) {
    clickListener.clicked(column, row);
  }

  public Optional<String> getColumn() {
    return Optional.ofNullable(column.get());
  }

  public NullableProperty<String> columnProperty() {
    return column;
  }

  public void setColumn(String column) {
    this.column.set(column);
  }

  public Optional<Integer> getRow() {
    return Optional.ofNullable(row.get());
  }

  public NullableProperty<Integer> rowProperty() {
    return row;
  }

  public void setRow(int row) {
    this.row.set(row);
  }

  /**
   * Turn the selection into an empty selection (i.e. no row/column selected).
   */
  public void clear() {
    this.row.set(null);
    this.column.set(null);
  }


  @Override
  public boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null || getClass() != obj.getClass()) {
      return false;
    }

    Selection selection = (Selection) obj;
    if (column.get() == null ? selection.column.get() != null
        : !column.get().equals(selection.column.get())) {
      return false;
    }
    return row.get() == null ? selection.row.get() == null : row.get().equals(selection.row.get());
  }

  @Override
  public int hashCode() {
    int result = Objects.hashCode(column.get());
    result = 31 * result + Objects.hashCode(row.get());
    return result;
  }
}
