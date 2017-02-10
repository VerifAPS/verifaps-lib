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
 * @author Benjamin Alt
 * @author Philipp
 */
public class SpecificationRow<C> implements Commentable, Observable {

  public static Callback<SpecificationRow, Observable[]> extractor() {
    return param -> new Observable[] { param };
  }

  private final ObservableMap<String, C> cells;
  private final StringProperty comment;

  private final List<InvalidationListener> listeners;
  private final Callback<C, Observable[]> extractor;
  private final InvalidationListener listenRowInvalidation;

  public static <E> SpecificationRow<E> createUnobservableRow(Map<String, E> cells) {
    return new SpecificationRow<>(cells, p -> new Observable[0]);
  }

  /*
  public SpecificationRow(Map<String, C> cells) {
    this(cells, param -> new Observable[] {});
  }*/

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

  private void cellsMapChanged(MapChangeListener.Change<? extends String, ? extends C> change) {
    if (change.wasAdded()) {
      subscribeToCell(change.getValueAdded());
    }
    if (change.wasRemoved()) {
      unsubscribeFromCell(change.getValueRemoved());
    }
  }

  private void subscribeToCell(C c) {
    for (Observable observable : extractor.call(c)) {
      observable.addListener(listenRowInvalidation);
    }
  }

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
    int result = cells.hashCode();
    result = 31 * result + (comment != null ? comment.hashCode() : 0);
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
