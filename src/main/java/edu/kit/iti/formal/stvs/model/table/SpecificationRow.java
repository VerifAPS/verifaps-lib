package edu.kit.iti.formal.stvs.model.table;

import javafx.beans.InvalidationListener;
import javafx.beans.Observable;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.collections.MapChangeListener;
import javafx.collections.ObservableMap;
import javafx.util.Callback;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * A row in a specification table (see {@link SpecificationTable}). The generic type parameter C
 * is the type of the cells.
 * @author Benjamin Alt
 */
public class SpecificationRow<C> implements Commentable, Observable {

  private final ObservableMap<String, C> cells;
  private final StringProperty comment;
  private final List<InvalidationListener> listeners;
  private final Callback<C, Observable[]> extractor;
  private final InvalidationListener listenRowInvalidation;

  /**
   * Create a row which is not observable. This is the case for rows in
   * {@link ConcreteSpecification}s and implemented via an empty extractor.
   * @param cells The cells of the unobservable row
   * @param <E> The type of the cells in the unobservable row
   * @return The created unobservable row
   */
  public static <E> SpecificationRow<E> createUnobservableRow(Map<String, E> cells) {
    return new SpecificationRow<>(cells, p -> new Observable[0]);
  }

  /**
   * Create a SpecificationRow from a given number of cells and an extractor. The extractor is
   * required for "deep observing", i.e. the registering of change listeners on the contents of
   * an observable collection (here, the collection of cells - to fire change events not only
   * when cells are added or removed, but also when properties in the cells change). For more
   * information on extractors, see https://docs.oracle
   * .com/javase/8/javafx/api/javafx/collections/FXCollections.html.
   * @param cells The initial cells of the row
   * @param extractor The extractor to be used for deep observing on the cells
   */
  public SpecificationRow(Map<String, C> cells, Callback<C, Observable[]> extractor) {
    this.cells = FXCollections.observableMap(cells);
    this.cells.addListener(this::cellsMapChanged);
    this.listeners = new ArrayList<>();
    this.comment = new SimpleStringProperty("");
    this.extractor = extractor;
    listenRowInvalidation = observable ->
        listeners.forEach(listener -> listener.invalidated(observable));
    this.cells.addListener(listenRowInvalidation);
    comment.addListener(listenRowInvalidation);
    cells.values().forEach(this::subscribeToCell);
  }

  /**
   * Called when cells were added or removed to this row.
   * @param change The change event
   */
  private void cellsMapChanged(MapChangeListener.Change<? extends String, ? extends C> change) {
    if (change.wasAdded()) {
      subscribeToCell(change.getValueAdded());
    }
    if (change.wasRemoved()) {
      unsubscribeFromCell(change.getValueRemoved());
    }
  }


  /**
   * Add an InvalidationListener to a certain cell.
   * @param c The cell to add a listener to
   */
  private void subscribeToCell(C c) {
    for (Observable observable : extractor.call(c)) {
      observable.addListener(listenRowInvalidation);
    }
  }

  /**
   * Remove an InvalidationListener from a certain cell
   * @param cell The cell to remove the listener from
   */
  private void unsubscribeFromCell(C cell) {
    for (Observable observable : extractor.call(cell)) {
      observable.removeListener(listenRowInvalidation);
    }
  }

  public ObservableMap<String,C> getCells() {
    return cells;
  }

  @Override
  public void setComment(String comment) {
    this.comment.set(comment);
  }

  @Override
  public String getComment() {
    return this.comment.get();
  }

  @Override
  public StringProperty commentProperty() {
    return comment;
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) return true;
    if (!(o instanceof SpecificationRow)) return false;

    SpecificationRow<?> that = (SpecificationRow<?>) o;

    if (!cells.equals(that.cells)) return false;
    return comment != null ? comment.get().equals(that.comment.get()) : that.comment == null;
  }

  @Override
  public int hashCode() {
    int result = getCells() != null ? getCells().hashCode() : 0;
    result = 31 * result + (getComment() != null ? getComment().hashCode() : 0);
    result = 31 * result + (listeners != null ? listeners.hashCode() : 0);
    result = 31 * result + (extractor != null ? extractor.hashCode() : 0);
    return result;
  }

  public String toString() {
    String map =
        String.join(", ",
            cells.entrySet().stream().map(entry ->
                entry.getKey() + ": " + entry.getValue()).collect(Collectors.toList()));
    return "SpecificationRow(comment: " + getComment() + ", " + map + ")";
  }

  @Override
  public void addListener(InvalidationListener listener) {
    listeners.add(listener);
  }

  @Override
  public void removeListener(InvalidationListener listener) {
    listeners.remove(listener);
  }

}
