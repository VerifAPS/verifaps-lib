package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.model.STVSRootModel;
import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;

import java.util.Comparator;
import java.util.List;

/**
 * Created by csicar on 09.01.17.
 */
public class STVSRootController implements Controller {
    private STVSRootView view;
    private STVSRootModel STVSRootModel;
    /**
     * Used to sort Types (Enums should be at the bottom)
     */
    private Comparator<Type> typeComparator;

    public STVSRootView getView() {
        return view;
    }
    public STVSRootController(){

    }

    private void onIOVariablesChange(List<IOVariable> ioVars){

    }
    private void onTypesChange(List<Type> types){

    }
}
