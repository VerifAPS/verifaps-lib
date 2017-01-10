package edu.kit.iti.formal.stvs.view;

import javafx.beans.NamedArg;
import javafx.scene.Parent;
import javafx.scene.Scene;

/**
 * Created by csicar on 09.01.17.
 */
public class STVSMainScene extends Scene {
    private STVSRootController rootController;
    public STVSMainScene(@NamedArg("root") Parent root) {
        super(root);
    }

    public STVSRootController getRootController() {
        return rootController;
    }

    public void setRootController(STVSRootController rootController) {
        this.rootController = rootController;
    }
}
