package edu.kit.iti.formal.stvs.view.spec.timingdiagram;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;

/**
 * Created by csicar on 09.01.17.
 * creates TimingDiagramCollectionView
 * gets created by SpecificationTabController; is toplevel class for timingdiagram-package
 */
public class TimingDiagramCollectionController implements Controller {
    private HybridSpecification spec;
    private GlobalConfig globalConfig;

    /**
     * creates VariableTimingDiagram for each given Variable
     *
     * @param spec
     * @param globalConfig
     */
    public TimingDiagramCollectionController(HybridSpecification spec, GlobalConfig globalConfig) {

        this.globalConfig = globalConfig;
    }

    public TimingDiagramCollectionView getView() {
        return null;
    }

}
