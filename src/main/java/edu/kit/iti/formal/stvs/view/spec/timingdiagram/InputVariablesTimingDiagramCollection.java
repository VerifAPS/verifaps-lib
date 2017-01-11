package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.common.VariableIdentifier;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import javafx.collections.ObservableList;

/**
 * Created by csicar on 09.01.17.
 */
public class InputVariablesTimingDiagramCollection extends CategoryTimingDiagramCollection {

    public InputVariablesTimingDiagramCollection(HybridSpecification concreteSpecification, ObservableList<VariableIdentifier> ioVariables, Selection selection, GlobalConfig globalConfig) {
        super(concreteSpecification, ioVariables);
        this.globalConfig = globalConfig;
    }
    private GlobalConfig globalConfig;
}
