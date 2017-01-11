package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;

/**
 * Controller for the set of either InputVariables TimingDiagramCollectionController or OutputVariables TimingDiagramCollectionController
 * Created by csicar on 09.01.17.
 */
public abstract class CategoryTimingDiagramCollection implements Controller {
    private CategoryTimingDiagramCollectionView view;
    private HybridSpecification spec;

    public CategoryTimingDiagramCollection(HybridSpecification spec) {

    }

    public CategoryTimingDiagramCollectionView getView() {
        return view;
    }

}
