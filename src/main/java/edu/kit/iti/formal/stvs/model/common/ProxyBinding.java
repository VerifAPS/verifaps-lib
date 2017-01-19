package edu.kit.iti.formal.stvs.model.common;

import javafx.beans.Observable;
import javafx.beans.binding.ObjectBinding;

/**
 * Created by leonk on 19.01.2017.
 */
public class ProxyBinding<T> extends ObjectBinding<T> {
  private final T wrappedValue;
  private final Observable[] bindings;

  /**
   * Calculates the current value of this binding.
   * The binding does only rely on its children, so it does not have
   * to compute a new value to become valid again.
   *
   * @return the current value
   */
  @Override
  protected T computeValue() {
    return wrappedValue;
  }

  /**
   * Unbind all children.
   */
  @Override
  public void dispose() {
    this.unbind(bindings);
  }

  /**
   * This creates a binding, something that takes listeners
   * and notifies them if it becomes invalid.
   * The binding becomes invalid if any of the given oberservables becomes invalid.
   * Therefore, it can be used to implement observables which hold observables as attributes.
   *
   * @param wrappedValue Object that holds the observables
   * @param observables  List of the Observables
   */
  public ProxyBinding(T wrappedValue, Observable... observables) {
    this.wrappedValue = wrappedValue;
    this.bindings = observables;
    this.bind(observables);
    //makes the Binding immediately valid again after invalidation
    this.addListener(invalid -> get());
  }
}
