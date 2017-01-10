package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.StringProperty;
import javafx.scene.Node;

import java.util.List;
import java.util.function.Consumer;

public class IOVariableNamePopupController implements Controller {
    private List<IOVariable> ioVars;
    private StringProperty name;
    /**
     * Is called if variable name was confirmed
     */
    private Consumer<String> variableChosenListener;

    public IOVariableNamePopupController(List<IOVariable> ioVariables, Consumer<String> variableChosenListener) {
    }

    @Override
    //Node is probably not the right type. Need to be changed in Implementation
    public Node getView() {
        return null;
    }
}
