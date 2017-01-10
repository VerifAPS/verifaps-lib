package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.view.editor.EditorPane;
import edu.kit.iti.formal.stvs.view.spec.SpecificationsPane;
import javafx.scene.layout.Pane;

/**
 * Created by csicar on 09.01.17.
 */
public class STVSRootView extends Pane {
    private STVSMenuBar menuBar;
    private EditorPane editor;
    private SpecificationsPane specifications;

    public STVSMenuBar getMenuBar() {
        return menuBar;
    }

    public EditorPane getEditor() {
        return editor;
    }

    public SpecificationsPane getSpecifications() {
        return specifications;
    }

    public void setMenuBar(STVSMenuBar menuBar) {
        this.menuBar = menuBar;
    }

    public void setEditor(EditorPane editor) {
        this.editor = editor;
    }

    public void setSpecifications(SpecificationsPane specifications) {
        this.specifications = specifications;
    }
}
