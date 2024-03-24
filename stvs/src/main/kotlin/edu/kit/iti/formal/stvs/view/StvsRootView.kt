package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.view.editor.EditorPane;
import edu.kit.iti.formal.stvs.view.spec.SpecificationsPane;
import javafx.scene.control.SplitPane;

/**
 * This view holds the editor and the specifications pane.
 *
 * @author Carsten Csiky
 */
public class StvsRootView extends SplitPane {
  private EditorPane editor;
  private SpecificationsPane specifications;

  /**
   * This creates an instance that holds an editor and the specifications pane.
   *
   * @param editor Editor to display
   * @param specifications Pane to display
   */
  public StvsRootView(EditorPane editor, SpecificationsPane specifications) {
    this.editor = editor;
    this.specifications = specifications;
    ViewUtils.setupClass(this);

    // for presentations
    //this.setStyle("-fx-font-size: 16pt");

    this.getItems().addAll(editor, specifications);
  }

  public EditorPane getEditor() {
    return editor;
  }

  public SpecificationsPane getSpecifications() {
    return specifications;
  }

  public void setEditor(EditorPane editor) {
    this.editor = editor;
    this.getItems().set(0, editor);
  }

  public void setSpecifications(SpecificationsPane specifications) {
    this.specifications = specifications;
  }
}
