package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.CodeIOVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIOVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.ObjectProperty;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;

public class ColumnHeaderController implements Controller {
    private ColumnHeader columnHeader;
    private final ObservableList<CodeIOVariable> codeVars;
    private final ObjectProperty<SpecIOVariable> columnName;
    private GlobalConfig globalConfig;
    private ContextMenu contextMenu;
    private ObservableList<Type> types;

    public ColumnHeaderController(ObservableList<Type> types, ObservableList<CodeIOVariable> codeVars, ObjectProperty<SpecIOVariable> columnName, GlobalConfig globalConfig) {
        this.types = types;
        this.codeVars = codeVars;
        this.columnName = columnName;
        this.globalConfig = globalConfig;
    }

    @Override
    public ColumnHeader getView() {
        return columnHeader;
    }
}
