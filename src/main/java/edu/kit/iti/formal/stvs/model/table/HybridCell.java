package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

/**
 * Created by Philipp on 01.02.2017.
 * @author Philipp
 */
public class HybridCell<C extends CellOperationProvider> implements CellOperationProvider {

  private final C cell;
  private final String column;
  private final ObservableList<String> counterExamples;

  public HybridCell(String column, C cell) {
    this.cell = cell;
    this.column = column;
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

  public String getColumn() {
    return column;
  }

  public void clearCounterExample() {
    counterExamples.setAll();
  }

  public ObservableList<String> counterExamplesProperty() {
    return counterExamples;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (o == null || getClass() != o.getClass()) return false;

    HybridCell<?> that = (HybridCell<?>) o;

    if (getCell() != null ? !getCell().equals(that.getCell()) : that.getCell() != null)
      return false;
    if (getColumn() != null ? !getColumn().equals(that.getColumn()) : that.getColumn() != null)
      return false;
    return counterExamples != null ? counterExamples.equals(that.counterExamples) : that.counterExamples == null;
  }

  @Override
  public int hashCode() {
    int result = getCell() != null ? getCell().hashCode() : 0;
    result = 31 * result + (getColumn() != null ? getColumn().hashCode() : 0);
    result = 31 * result + (counterExamples != null ? counterExamples.hashCode() : 0);
    return result;
  }
}
