package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.collections.ObservableList;
import javafx.scene.Node;

/**
 * Created by csicar on 10.01.17.
 */
public class SpecFileChooserController implements Controller {
    private GlobalConfig globalConfig;
    public SpecFileChooserController(ObservableList<HybridSpecification> hybridSpecifications, GlobalConfig globalConfig) {

        this.globalConfig = globalConfig;
    }

    @Override
    public Node getView() {
        return null;
    }
}
