package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.table.ConcreteDuration;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.scene.control.ContextMenu;

import java.util.List;
import java.util.function.Function;

/**
 * Controller for the Cycle-Display on the X-Axis
 * Created by csicar on 10.01.17.
 */
public class CycleController implements Controller {
    private ContextMenu contextMenu;

    public CycleController(HybridSpecification spec,  Selection selection) {

    }

    public CycleView getView() {
        return null;
    }
}
