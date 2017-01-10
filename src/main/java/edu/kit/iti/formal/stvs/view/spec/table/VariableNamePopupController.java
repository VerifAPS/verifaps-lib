package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import javafx.beans.property.StringProperty;

import java.util.List;

public class VariableNamePopupController {
    private List<IOVariable> ioVars;
    private StringProperty name;
    private CategoryTableController parent;

    public VariableNamePopupController(List<String> ioVariables, boolean editable, CategoryTableController parent) {
    }
}
