package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

/**
 * <p>The model for a cell (for
 * {@link edu.kit.iti.formal.stvs.view.spec.table.SpecificationTableCell})
 * that both has an abstract cell model, a {@link CellOperationProvider} (that is, either a
 * {@link ConstraintCell} or {@link ConstraintDuration}), and a list of counterexample
 * strings that should be viewed in-place below these cells.</p>
 *
 * <p>Created by Philipp on 01.02.2017.</p>
 *
 * @author Philipp
 */
public class HybridCell<C extends CellOperationProvider> implements CellOperationProvider {

  private final C cell;
  private final ObservableList<String> counterExamples;

  /**
   * Creates a hybrid-cell for given constraint cell or duration without any counter example
   * cells.
   *
   * @param cell the constraint duration or cell
   */
  public HybridCell(C cell) {
    this.cell = cell;
    this.counterExamples = FXCollections.observableArrayList();
  }

  public C getCell() {
    return this.cell;
  }

  @Override
  public void setComment(String comment) {
    cell.setComment(comment);
  }

  @Override
  public String getComment() {
    return cell.getComment();
  }

  @Override
  public StringProperty commentProperty() {
    return cell.commentProperty();
  }

  @Override
  public String getAsString() {
    return cell.getAsString();
  }

  @Override
  public void setFromString(String input) {
    cell.setFromString(input);
  }

  @Override
  public StringProperty stringRepresentationProperty() {
    return cell.stringRepresentationProperty();
  }

  /**
   * Makes all counterexample cells disappear. After this call
   * <tt>{@link #counterExamplesProperty()}.isEmpty()</tt> is true.
   */
  public void clearCounterExample() {
    counterExamples.setAll();
  }

  public ObservableList<String> counterExamplesProperty() {
    return counterExamples;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }

    HybridCell<?> that = (HybridCell<?>) o;

    if (getCell() != null ? !getCell().equals(that.getCell()) : that.getCell() != null) {
      return false;
    }
    return counterExamples != null ? counterExamples.equals(that.counterExamples)
        : that.counterExamples == null;
  }

  @Override
  public int hashCode() {
    int result = getCell() != null ? getCell().hashCode() : 0;
    result = 31 * result + (counterExamples != null ? counterExamples.hashCode() : 0);
    return result;
  }
}
