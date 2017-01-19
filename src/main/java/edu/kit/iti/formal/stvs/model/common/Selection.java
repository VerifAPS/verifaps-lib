package edu.kit.iti.formal.stvs.model.common;

import javafx.beans.InvalidationListener;
import javafx.beans.Observable;
import javafx.beans.property.IntegerProperty;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

/**
 * Created by csicar on 10.01.17.
 */
public class Selection implements Observable {

  private OptionalPropertyBase<String, StringProperty> column;
  private OptionalPropertyBase<Number, IntegerProperty> row;
  private ProxyBinding<Selection> proxyBinding;

  public Selection(String column, int row) {
    this.column = new OptionalPropertyBase<>(new SimpleStringProperty(column));
    this.row = new OptionalPropertyBase<>(new SimpleIntegerProperty(row));
    initBinding();
  }

  private void initBinding() {
    proxyBinding = new ProxyBinding<Selection>(this, column, row);
  }

  public Selection() {
    this.column = OptionalPropertyBase.ofNull(new SimpleStringProperty());
    this.row = OptionalPropertyBase.ofNull(new SimpleIntegerProperty());
    initBinding();
  }

  public String getColumn() {
    return column.get();
  }

  public OptionalPropertyBase<String, StringProperty> columnProperty() {
    return column;
  }

  public void setColumn(String column) {
    this.column.set(column);
  }

  public int getRow() {
    return row.get().intValue();
  }

  public OptionalPropertyBase<Number, IntegerProperty> rowProperty() {
    return row;
  }

  public void setRow(int row) {
    this.row.set(row);
  }

  /**
   * Adds an {@link InvalidationListener} which will be notified whenever the
   * {@code Observable} becomes invalid. If the same
   * listener is added more than once, then it will be notified more than
   * once. That is, no check is made to ensure uniqueness.
   * <p>
   * Note that the same actual {@code InvalidationListener} instance may be
   * safely registered for different {@code Observables}.
   * <p>
   * The {@code Observable} stores a strong reference to the listener
   * which will prevent the listener from being garbage collected and may
   * result in a memory leak. It is recommended to either unregister a
   * listener by calling {@link #removeListener(InvalidationListener)
   * removeListener} after use or to use an instance of
   * {@link WeakInvalidationListener} avoid this situation.
   *
   * @param listener The listener to register
   * @throws NullPointerException if the listener is null
   * @see #removeListener(InvalidationListener)
   */
  @Override
  public void addListener(InvalidationListener listener) {
    proxyBinding.addListener(listener);
  }

  /**
   * Removes the given listener from the list of listeners, that are notified
   * whenever the value of the {@code Observable} becomes invalid.
   * <p>
   * If the given listener has not been previously registered (i.e. it was
   * never added) then this method call is a no-op. If it had been previously
   * added then it will be removed. If it had been added more than once, then
   * only the first occurrence will be removed.
   *
   * @param listener The listener to remove
   * @throws NullPointerException if the listener is null
   * @see #addListener(InvalidationListener)
   */
  @Override
  public void removeListener(InvalidationListener listener) {
    proxyBinding.removeListener(listener);
  }
}
