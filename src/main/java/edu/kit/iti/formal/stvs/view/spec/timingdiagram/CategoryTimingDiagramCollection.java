package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.table.concrete.ConcreteDuration;
import edu.kit.iti.formal.stvs.model.table.concrete.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.hybrid.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.ObservableList;

import java.util.function.Function;

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
