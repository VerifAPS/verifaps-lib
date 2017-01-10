package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.common.VariableIdentifier;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.ObservableList;

public class ColumnHeaderController implements Controller {
    private ColumnHeader columnHeader;

    public ColumnHeaderController(ObservableList<Type> types, ObservableList<IOVariable> ioVars, ObjectProperty<VariableIdentifier> ioVar) {
    }

    @Override
    public ColumnHeader getView() {
        return null;
    }
}
