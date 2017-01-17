package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.scene.Node;
import javafx.scene.control.ContextMenu;

/**
 * Created by csicar on 09.01.17.
 * Controller for a single TimingDiagramController e.g. for <b>one</b> Variable and over all Timesteps
 */
public class TimingDiagramController implements Controller {
    private ContextMenu contextMenu;
    private TimingDiagramView view;

    public TimingDiagramController(SpecIoVariable ioVariable, HybridSpecification spec, Selection selection) {

    }

    /**
     * sets the selection on selection
     * @param selection selected node
     */
    private void onSelection(Node selection) {

    }

    public TimingDiagramView getView() {
        return null;
    }
}
