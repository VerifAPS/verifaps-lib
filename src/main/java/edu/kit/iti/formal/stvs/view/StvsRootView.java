package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.view.editor.EditorPane;
import edu.kit.iti.formal.stvs.view.spec.SpecificationsPane;
import javafx.scene.control.SplitPane;

/**
 * Created by csicar on 09.01.17.
 */
public class StvsRootView extends SplitPane {
  private EditorPane editor;
  private SpecificationsPane specifications;

  public StvsRootView(EditorPane editor, SpecificationsPane specifications) {
    this.editor = editor;
    this.specifications = specifications;


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
