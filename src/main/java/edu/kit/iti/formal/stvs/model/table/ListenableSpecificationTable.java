package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.beans.property.ObjectProperty;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;

import java.util.HashMap;
import java.util.Map;
import java.util.NoSuchElementException;

/**
 * Created by bal on 22.01.17.
 */
public abstract class ListenableSpecificationTable<C extends CellOperationProvider,D extends CellOperationProvider> extends SpecificationTable<C,D> {

  class SpecificationChangedListener<T> implements ChangeListener<T> {

    @Override
    public void changed(ObservableValue<? extends T> observableValue, T t, T t1) {
      onSpecificationChanged();
    }
  }

  @Override
  public void addColumn(String columnId, SpecificationColumn<C> column) {
    super.addColumn(columnId, column);
    column.getSpecIoVariable().categoryProperty().addListener(new SpecificationChangedListener<VariableCategory>());
    column.getSpecIoVariable().nameProperty().addListener(new SpecificationChangedListener<String>());
    column.getSpecIoVariable().typeProperty().addListener(new SpecificationChangedListener<Type>());
    for (int i = 0; i < durations.size(); i++) {
      C cell = column.getCellForRow(i);
      cell.stringRepresentationProperty().addListener(new SpecificationChangedListener<String>());
      // No need to listen for changes to comments, as they have no effect (annotations would)
    }
  }

  public void removeColumn(String columnId) {
    super.removeColumn(columnId);
    onSpecificationChanged();
  }

  public void addRow(int rowNum, SpecificationRow<C, D> row) {
    super.addRow(rowNum, row);
    for (String varName : columns.keySet()) {
      row.getCellForVariable(varName).stringRepresentationProperty().addListener(new SpecificationChangedListener<String>());
    }
    row.getDuration().stringRepresentationProperty().addListener(new SpecificationChangedListener<String>());
  }

  public void removeRow(int rowNum) {
    super.removeRow(rowNum);
    onSpecificationChanged();
  }

  abstract void onSpecificationChanged();
}
