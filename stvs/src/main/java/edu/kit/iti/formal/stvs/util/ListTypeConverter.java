package edu.kit.iti.formal.stvs.util;

import java.util.List;

import javafx.beans.property.ObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

/**
 * Util class for conversion of ObservableLists.
 *
 * @author Carsten Csiky
 */
public class ListTypeConverter {

  /**
   * Creates a {@link ObservableList}.
   *
   * @param list property of the list to convert
   * @param <E> type of the list elements
   * @return observable list
   */
  public static <E> ObservableList<E> makeObservableList(ObjectProperty<List<E>> list) {
    ObservableList<E> observableList = FXCollections.observableList(list.get());
    list.addListener((observableValue, oldList, newList) -> observableList.setAll(newList));
    return observableList;
  }

}
