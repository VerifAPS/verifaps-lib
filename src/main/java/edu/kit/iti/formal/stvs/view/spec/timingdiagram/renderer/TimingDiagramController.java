package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.table.SpecificationColumn;
import edu.kit.iti.formal.stvs.model.table.concrete.ConcreteCell;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.scene.Node;
import java.util.List;
import java.util.function.Function;

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
    public TimingDiagramController(IOVariable ioVariable, SpecificationColumn<ConcreteCell> ioVarValues) {

    }

    /**
     * will be registered on all data-points similar to http://stackoverflow.com/questions/25892695/tooltip-on-line-chart-showing-date
     * this event will be bubbled up to the specificationTabController which will change the selection
     */
    private void onMouseOver(Node selection) {

    }

    public TimingDiagramView getView() {
        return null;
    }
}
