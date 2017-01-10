package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.collections.ObservableList;
import javafx.collections.transformation.SortedList;

import java.util.Comparator;

/**
 * Created by csicar on 09.01.17.
 */
public class STVSRootController implements Controller {
    private ObservableList<Type> types;
    private SortedList<Type> sortedTyes;
    /**
     * Used to sort Types (Enums should be at the bottom)
     */
    private Comparator<Type> typeComparator;
    private Code code;

    public STVSRootView getView() {
        return null;
    }
}
