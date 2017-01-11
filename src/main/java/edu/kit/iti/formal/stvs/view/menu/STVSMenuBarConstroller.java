package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;

/**
 * Created by csicar on 10.01.17.
 * Controller for the MenuBar at the top of the window
 * does just fire to the root controller
 */
public class STVSMenuBarConstroller implements Controller {
    private STVSMenuBar view;
    private GlobalConfig globalConfig;

    public STVSMenuBarConstroller(GlobalConfig config, GlobalConfig globalConfig) {

        this.globalConfig = globalConfig;
    }

    @Override
    public STVSMenuBar getView() {
        return view;
    }
}
