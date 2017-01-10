package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.table.SpecificationTable;
import edu.kit.iti.formal.stvs.model.table.constraint.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.constraint.ConstraintDuration;
import edu.kit.iti.formal.stvs.model.table.hybrid.HybridSpecification;
import javafx.collections.ObservableList;

import java.util.function.Consumer;

public class OutputTableController extends CategoryTableController {
    public OutputTableController(HybridSpecification spec, ObservableList<Type> types, ObservableList<IOVariable> ioVars, TablePaneController tablePaneController) {
        super("Output Variables", spec, types, ioVars, tablePaneController);
    }

    public void addIOVariable(String string) {

    }
}
