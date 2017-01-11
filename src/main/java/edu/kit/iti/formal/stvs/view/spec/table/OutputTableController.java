package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIOVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import javafx.collections.ObservableList;

public class OutputTableController extends CategoryTableController {
    private GlobalConfig globalConfig;
    public OutputTableController(HybridSpecification spec, ObservableList<Type> types, ObservableList<CodeIOVariable> ioVars, TablePaneController tablePaneController, GlobalConfig globalConfig) {
        super("Output Variables", spec, types, ioVars, tablePaneController);
        this.globalConfig = globalConfig;
    }

    public void addIOVariable(String string) {

    }
}
