package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import javafx.collections.ObservableList;

public class InputTableController extends CategoryTableController {
    public InputTableController(HybridSpecification spec, ObservableList<Type> types, ObservableList<IOVariable> ioVars, TablePaneController tablePaneController) {
        super("Input Variables", spec, types, ioVars, tablePaneController);
    }

    public void addIOVariable(String string) {

    }
}
