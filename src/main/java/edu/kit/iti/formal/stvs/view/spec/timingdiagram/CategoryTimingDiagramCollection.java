package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.model.common.VariableIdentifier;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.ObservableList;
import javafx.scene.control.ContextMenu;

/**
 * Controller for the set of either InputVariables TimingDiagramCollectionController or OutputVariables TimingDiagramCollectionController
 * Created by csicar on 09.01.17.
 */
public abstract class CategoryTimingDiagramCollection implements Controller {
    private CategoryTimingDiagramCollectionView view;
    private HybridSpecification spec;
    private ContextMenu contextMenu;

    public CategoryTimingDiagramCollection(HybridSpecification spec, ObservableList<VariableIdentifier> ioVariables) {

    }

    public CategoryTimingDiagramCollectionView getView() {
        return view;
    }

}
