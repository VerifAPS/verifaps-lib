package edu.kit.iti.formal.stvs.util;

import java.util.List;

import javafx.beans.property.ObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

/**
 * Created by csicar on 07.02.17.
 *
 * @author Carsten Csiky
 */
public class ListTypeConverter {

  public static <E> ObservableList<E> makeObservableList(ObjectProperty<List<E>> list) {
    ObservableList<E> observableList = FXCollections.observableList(list.get());
    list.addListener((observableValue, oldList, newList) -> observableList.setAll(newList));
    return observableList;
  }

}
