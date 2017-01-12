package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import javafx.scene.control.ContextMenu;

public class TableInputController extends TableCategoryController {

    public TableInputController(HybridSpecification spec, TablePaneController tablePaneController) {
        super("Input", spec, tablePaneController);
    }

    public void addIOVariable(String string) {

    }
    private GlobalConfig globalConfig;
    private ContextMenu contextMenu;
}
