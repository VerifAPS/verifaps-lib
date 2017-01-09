package edu.kit.iti.formal.stvs.view;

import javafx.collections.ObservableList;
import javafx.collections.transformation.SortedList;

import java.util.Comparator;

/**
 * Created by csicar on 09.01.17.
 */
public class STVSRootController {
    ObservableList<Type> types;
    SortedList<Type> sortedTyes;
    /**
     * Used to sort Types (Enums should be at the bottom)
     */
    Comparator<Type> typeComparator;
    Code code;
}
