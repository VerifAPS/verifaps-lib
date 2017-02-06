package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.table.CellOperationProvider;
import javafx.beans.property.StringProperty;

/**
 * Created by Philipp on 01.02.2017.
 */
public class HybridCellModel<C extends CellOperationProvider> implements CellOperationProvider {

  private final C cell;
  // TODO: private final ObservableList<String> counterExamples

  public HybridCellModel(C cell) {
    this.cell = cell;
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
}
