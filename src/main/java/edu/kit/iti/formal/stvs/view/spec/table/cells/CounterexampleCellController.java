package edu.kit.iti.formal.stvs.view.spec.table.cells;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.scene.control.ContextMenu;

public class CounterexampleCellController implements Controller {
    private GlobalConfig globalConfig;
    private String text;
    private CounterexampleCell counterexampleCell;
    private ContextMenu contextMenu;

    public CounterexampleCellController(String string, GlobalConfig globalConfig) {
        this.globalConfig = globalConfig;
    }

    @Override
    public CounterexampleCell getView() {
        return counterexampleCell;
    }
}