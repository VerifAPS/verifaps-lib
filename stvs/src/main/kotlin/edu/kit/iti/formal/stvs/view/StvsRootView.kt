package edu.kit.iti.formal.stvs.view

import edu.kit.iti.formal.stvs.view.editor.EditorPane
import edu.kit.iti.formal.stvs.view.spec.SpecificationsPane
import javafx.scene.control.SplitPane

/**
 * This view holds the editor and the specifications pane.
 *
 * @author Carsten Csiky
 */
class StvsRootView(ed: EditorPane, var specifications: SpecificationsPane) : SplitPane() {
    var editor: EditorPane = ed
        set(value) {
            field = editor; items[0] = value
        }


    /**
     * This creates an instance that holds an editor and the specifications pane.
     *
     * @param editor Editor to display
     * @param specifications Pane to display
     */
    init {
        ViewUtils.setupClass(this)
        // for presentations
        //this.setStyle("-fx-font-size: 16pt");
        items.addAll(editor, specifications)
    }
}
