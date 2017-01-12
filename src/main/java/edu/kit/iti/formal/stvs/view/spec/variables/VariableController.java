package edu.kit.iti.formal.stvs.view.spec.variables;

import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.scene.Node;
import javafx.scene.control.ContextMenu;

/**
 * Created by csicar on 10.01.17.
 */
public class VariableController implements Controller {
    private FreeVariable freeVariable;
    private VariableView view;
    private ContextMenu contextMenu;

    public VariableController(FreeVariable freeVariable) {
        this.freeVariable = freeVariable;
    }


    @Override
    public Node getView() {
        return null;
    }
}
