package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.model.common.Selection;
import edu.kit.iti.formal.stvs.model.common.SpecIOVariable;
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
public abstract class CategoryTimingDiagramCollectionController implements Controller {
    private CategoryTimingDiagramCollectionView view;
    private HybridSpecification spec;
    private ContextMenu contextMenu;
    private ObservableList<SpecIOVariable> definedVariables;

    public CategoryTimingDiagramCollectionController(HybridSpecification spec, ObservableList<SpecIOVariable> definedVariables, GlobalConfig config, Selection selection) {

    }

    public CategoryTimingDiagramCollectionView getView() {
        return view;
    }

}
