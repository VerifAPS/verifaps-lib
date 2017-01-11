package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.common.VariableIdentifier;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import javafx.collections.ObservableList;

/**
 * Created by csicar on 09.01.17.
 */
public class OutputVariablesTimingDiagramCollection extends CategoryTimingDiagramCollection {
    public OutputVariablesTimingDiagramCollection(HybridSpecification concreteSpecification, ObservableList<VariableIdentifier> ioVariables, Selection selection) {
        super(concreteSpecification, ioVariables);
    }
}
