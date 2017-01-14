package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIOVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.StringProperty;
import javafx.scene.Node;

import java.util.List;
import java.util.function.Consumer;

public class IOVariableNamePopupController implements Controller {
    private List<CodeIOVariable> ioVars;
    private StringProperty name;
    private IOVariableNamePopup ioVariableNamePopup;
    private GlobalConfig globalConfig;
    /**
     * @param variableChosenListener Is called if variable name was confirmed
     * @param globalConfig
     */
    public IOVariableNamePopupController(List<CodeIOVariable> ioVariables, Consumer<String> variableChosenListener, GlobalConfig globalConfig) {
        this.globalConfig = globalConfig;
    }

    @Override
    //Node is probably not the right type. Need to be changed in Implementation
    public Node getView() {
        return null;
    }
}
