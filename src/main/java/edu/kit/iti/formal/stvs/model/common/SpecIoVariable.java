package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.beans.InvalidationListener;
import javafx.beans.Observable;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;

/**
 * Created by csicar on 11.01.17.
 */
public class SpecIoVariable extends IoVariable implements Observable {
  private final ProxyBinding<SpecIoVariable> proxyBinding;
  private StringProperty name;
  private ObjectProperty<Type> type;
  private ObjectProperty<VariableCategory> category;

  /**
   * Creates a variable that appears in the specification.
   *
   * @param category The category of the variable
   * @param type     The type of the variable
   * @param name     The name of the Variable
   */
  public SpecIoVariable(VariableCategory category, Type type, String name) {
    this.category = new SimpleObjectProperty<>(category);
    this.type = new SimpleObjectProperty<>(type);
    this.name = new SimpleStringProperty(name);
    this.proxyBinding = new ProxyBinding<SpecIoVariable>(
        this,
        this.category,
        this.type,
        this.name
    );
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
  public Type getType() {
    return type.get();
  }

  public ObjectProperty<Type> typeProperty() {
    return type;
  }

  public void setType(Type type) {
    this.type.set(type);
  }

  @Override
  public VariableCategory getCategory() {
    return category.get();
  }

  public ObjectProperty<VariableCategory> categoryProperty() {
    return category;
  }

  public void setCategory(VariableCategory category) {
    this.category.set(category);
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
