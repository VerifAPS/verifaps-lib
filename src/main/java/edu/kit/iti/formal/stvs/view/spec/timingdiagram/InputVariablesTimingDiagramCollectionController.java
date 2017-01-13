package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.common.SpecIOVariable;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import javafx.collections.ObservableList;

/**
 * Created by csicar on 09.01.17.
 */
public class InputVariablesTimingDiagramCollectionController extends CategoryTimingDiagramCollectionController {

    public InputVariablesTimingDiagramCollectionController(HybridSpecification spec, ObservableList<SpecIOVariable> definedVariables, GlobalConfig config, Selection selection) {
        super(spec, definedVariables, config, selection);
    }
}
