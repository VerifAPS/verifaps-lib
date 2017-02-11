package edu.kit.iti.formal.stvs.util;

import javafx.beans.property.ObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

import java.util.List;

/**
 * Created by csicar on 07.02.17.
 */
public class ListTypeConverter {

  public static <E> ObservableList<E> makeObservableList(ObjectProperty<List<E>> list) {
    ObservableList<E> observableList = FXCollections.observableList(list.get());
    list.addListener((observableValue, oldList, newList) -> observableList.setAll(newList));
    return observableList;
  }

}
