package edu.kit.iti.formal.stvs.view.spec.table.cells;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.StringProperty;
import javafx.scene.control.ContextMenu;

public class ValueCellController implements Controller {
    private ValueCell valueCell;
    private GlobalConfig globalConfig;
    private ContextMenu contextMenu;
    /**
     * Listens if model cell changes
     */
    private void onAddUserInputStringChanged(String string){}
    private StringProperty value;

    public ValueCellController(ConstraintCell constraintCell, GlobalConfig globalConfig) {
        this.globalConfig = globalConfig;
    }

    @Override
    public ValueCell getView() {
        return valueCell;
    }
}
