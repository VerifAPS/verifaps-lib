package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.table.CellOperationProvider;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

/**
 * Created by Philipp on 01.02.2017.
 */
public class HybridCellModel<C extends CellOperationProvider> implements CellOperationProvider {

  private final C cell;
  private final String column;
  private final ObservableList<String> counterExamples;

  public HybridCellModel(String column, C cell) {
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
}
