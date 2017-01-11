package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import javafx.collections.ObservableList;

/**
 * Created by csicar on 10.01.17.
 */
public class SpecFileChooserController {
    private GlobalConfig globalConfig;
    public SpecFileChooserController(ObservableList<HybridSpecification> hybridSpecifications, GlobalConfig globalConfig) {

        this.globalConfig = globalConfig;
    }

}
