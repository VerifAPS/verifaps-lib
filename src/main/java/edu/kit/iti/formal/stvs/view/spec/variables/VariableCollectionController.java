package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.scene.Node;
import javafx.scene.control.ContextMenu;

/**
 * Created by csicar on 10.01.17.
 */
public class VariableCollectionController implements Controller{
    private FreeVariableSet freeVariableSet;
    private VariableCollection view;
    private ContextMenu contextMenu;

    public VariableCollectionController(FreeVariableSet freeVariableSet) {
        this.freeVariableSet = freeVariableSet;
    }

    @Override
    public VariableCollection getView() {
        return view;
    }
}
