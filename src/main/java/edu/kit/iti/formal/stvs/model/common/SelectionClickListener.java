package edu.kit.iti.formal.stvs.model.common;

/**
 * {@code SelectionClickListener} gets invoked by {@link Selection} and indicates that the user
 * clicked on a view that represents a cell in the
 * {@link edu.kit.iti.formal.stvs.model.table.HybridSpecification}.
 */
@FunctionalInterface
public interface SelectionClickListener {
  /**
   * Must handle a click event that can be assigned to a cell in a
   * {@link edu.kit.iti.formal.stvs.model.table.HybridSpecification}
   *
   * @param columnName Name of the column that the event can be assigned to
   * @param rowNumber Number of the row that the event can be assigned to
   */
  void clicked(String columnName, Integer rowNumber);
}
