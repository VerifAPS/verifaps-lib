package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;

/**
 * Created by csicar on 10.01.17.
 */
public class VariableCollectionController implements Controller{
    private ObservableList<Type> codeTypes;
    private FreeVariableSet freeVariableSet;
    private VariableCollection view;
    private ContextMenu contextMenu;

    public VariableCollectionController(ObservableList<Type> codeTypes, FreeVariableSet freeVariableSet) {
        this.codeTypes = codeTypes;
        this.freeVariableSet = freeVariableSet;
    }

    @Override
    public VariableCollection getView() {
        return view;
    }
}
