package edu.kit.iti.formal.stvs.util;

import javafx.beans.InvalidationListener;
import javafx.beans.property.ObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;

/**
 * Created by csicar on 07.02.17.
 */
public class ListTypeConverter {

  public static <E> ObservableList<E> makeObservableList(ObjectProperty<List<E>> list) {
    ObservableList<E> observableList = FXCollections.observableList(list.get());
    list.addListener((observableValue, oldList, newList) -> {
      observableList.clear();
      observableList.addAll(newList);
    });
    return observableList;
  }

}
