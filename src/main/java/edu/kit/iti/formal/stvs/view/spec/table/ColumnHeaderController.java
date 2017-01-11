package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIOVariable;
import edu.kit.iti.formal.stvs.model.common.VariableIdentifier;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.ObjectProperty;
import javafx.collections.ObservableList;

public class ColumnHeaderController implements Controller {
    private ColumnHeader columnHeader;
    private GlobalConfig globalConfig;

    public ColumnHeaderController(ObservableList<Type> types, ObservableList<CodeIOVariable> ioVars, ObjectProperty<VariableIdentifier> ioVar, GlobalConfig globalConfig) {
        this.globalConfig = globalConfig;
    }

    @Override
    public ColumnHeader getView() {
        return columnHeader;
    }
}
