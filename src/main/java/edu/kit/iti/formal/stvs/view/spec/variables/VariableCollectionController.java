package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.scene.Node;

/**
 * Created by csicar on 10.01.17.
 */
public class VariableCollectionController implements Controller{
    private FreeVariableSet freeVariableSet;
    private VariableCollection view;

    public VariableCollectionController(FreeVariableSet freeVariableSet) {
        this.freeVariableSet = freeVariableSet;
    }

    @Override
    public VariableCollection getView() {
        return view;
    }
}
