package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.table.SpecificationColumn;
import edu.kit.iti.formal.stvs.model.table.concrete.ConcreteCell;

/**
 * Created by csicar on 09.01.17.
 * Controller for a single TimingDiagram e.g. for <b>one</b> Variable and over all Timesteps
 */
public class TimingDiagram {
    public TimingDiagramView view;

    public TimingDiagram(IOVariable ioVariable, SpecificationColumn<ConcreteCell> ioVarValues) {

    }

    /**
     * will be registered on all datapoints similar to http://stackoverflow.com/questions/25892695/tooltip-on-line-chart-showing-date
     * this event will be bubbled up to the specificationTabController which will change the selection
     */
    private void onMouseOver() {

    }
}
