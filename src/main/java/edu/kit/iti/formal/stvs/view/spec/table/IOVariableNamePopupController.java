package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import javafx.beans.property.StringProperty;

import java.util.List;
import java.util.function.Consumer;

public class IOVariableNamePopupController {
    private List<IOVariable> ioVars;
    private StringProperty name;
    /**
     * Is called if variable name was confirmed
     */
    private Consumer<String> variableChosenListener;

    public IOVariableNamePopupController(List<IOVariable> ioVariables, Consumer<String> variableChosenListener) {
    }
}
