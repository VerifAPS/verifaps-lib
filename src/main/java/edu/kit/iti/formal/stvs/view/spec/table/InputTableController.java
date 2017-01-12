package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIOVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;

public class InputTableController extends CategoryTableController {
    public InputTableController(HybridSpecification spec, ObservableList<Type> types, ObservableList<CodeIOVariable> ioVars, TablePaneController tablePaneController, GlobalConfig globalConfig) {
        super("Input Variables", spec, types, ioVars, tablePaneController);
        this.globalConfig = globalConfig;
    }

    public void addIOVariable(String string) {

    }
    private GlobalConfig globalConfig;
    private ContextMenu contextMenu;
}
