package edu.kit.iti.formal.stvs.view;

import javafx.beans.NamedArg;
import javafx.scene.Parent;
import javafx.scene.Scene;
import javafx.scene.control.ContextMenu;

/**
 * Created by csicar on 09.01.17.
 */
public class STVSMainScene extends Scene {
    private STVSRootController rootController;
    private ContextMenu contextMenu;

    public STVSMainScene(Parent root) {
        super(root);
    }

    public STVSRootController getRootController() {
        return rootController;
    }

    public void setRootController(STVSRootController rootController) {
        this.rootController = rootController;
    }
}
