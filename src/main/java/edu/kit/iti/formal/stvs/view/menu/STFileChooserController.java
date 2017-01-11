package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.scene.Node;

/**
 * Created by csicar on 10.01.17.
 */
public class STFileChooserController implements Controller {
    public STFileChooserController(Code code, GlobalConfig globalConfig) {

        this.globalConfig = globalConfig;
    }
    private GlobalConfig globalConfig;

    @Override
    public Node getView() {
        return null;
    }
}
