package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import javafx.collections.ObservableList;

public class InputTableController extends CategoryTableController {
    public InputTableController(HybridSpecification spec, ObservableList<Type> types, ObservableList<IOVariable> ioVars, TablePaneController tablePaneController, GlobalConfig globalConfig) {
        super("Input Variables", spec, types, ioVars, tablePaneController);
        this.globalConfig = globalConfig;
    }

    public void addIOVariable(String string) {

    }
    private GlobalConfig globalConfig;
}
