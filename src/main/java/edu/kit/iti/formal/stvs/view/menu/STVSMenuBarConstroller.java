package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.STVSRootController;

/**
 * Created by csicar on 10.01.17.
 * Controller for the MenuBar at the top of the window
 * does just fire to the root controller
 */
public class STVSMenuBarConstroller implements Controller {
    private STVSMenuBar view;

    public STVSMenuBarConstroller(STVSRootController rootController) {

    }

    @Override
    public STVSMenuBar getView() {
        return view;
    }
}
