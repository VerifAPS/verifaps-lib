package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.model.common.CodeIOVariable;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.common.SpecIOVariable;
import edu.kit.iti.formal.stvs.model.table.SpecificationColumn;
import edu.kit.iti.formal.stvs.model.table.ConcreteCell;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.scene.Node;

/**
 * Created by csicar on 09.01.17.
 * Controller for a single TimingDiagramController e.g. for <b>one</b> Variable and over all Timesteps
 */
public class TimingDiagramController implements Controller {
    public TimingDiagramView view;

    /**
     *TimingDiagramController
     * @param ioVariable
     * @param ioVarValues
     */
    public TimingDiagramController(SpecIOVariable ioVariable, SpecificationColumn<ConcreteCell> ioVarValues, Selection selection) {

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
