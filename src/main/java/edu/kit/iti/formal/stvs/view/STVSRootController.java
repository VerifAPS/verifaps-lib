package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.collections.ObservableList;
import javafx.collections.transformation.SortedList;

import java.util.Comparator;
import java.util.List;

/**
 * Created by csicar on 09.01.17.
 */
public class STVSRootController implements Controller {
    private STVSRootView view;
    private ObservableList<Type> types;
    private SortedList<Type> sortedTyes;
    private ObservableList<IOVariable> ioVars;
    private Code code;
    /**
     * Used to sort Types (Enums should be at the bottom)
     */
    private Comparator<Type> typeComparator;

    public STVSRootView getView() {
        return view;
    }
    public STVSRootController(){

    }

    public Code getCode() {
        return code;
    }

    private void onIOVariablesChange(List<IOVariable> ioVars){

    }
    private void onTypesChange(List<Type> types){

    }
}
