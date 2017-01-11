package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;

/**
 * Created by csicar on 09.01.17.
 * creates TimingDiagramCollectionView
 * gets created by SpecificationTabController; is toplevel class for timingdiagram-package
 */
public class TimingDiagramCollectionController implements Controller {
    private HybridSpecification spec;


    /**
     * creates VariableTimingDiagram for each given Variable
     *
     * @param spec
     */
    public TimingDiagramCollectionController(HybridSpecification spec) {

    }

    public TimingDiagramCollectionView getView() {
        return null;
    }

}
