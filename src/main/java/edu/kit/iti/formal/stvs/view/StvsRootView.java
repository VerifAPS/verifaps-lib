package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.view.menu.StvsMenuBar;
import edu.kit.iti.formal.stvs.view.editor.EditorPane;
import javafx.scene.control.SplitPane;
import javafx.scene.control.TabPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;

/**
 * Created by csicar on 09.01.17.
 */
public class StvsRootView extends SplitPane {
  private EditorPane editor;
  private TabPane specifications;

  public StvsRootView(EditorPane editor, TabPane specifications) {
    this.editor = editor;
    this.specifications = specifications;

    this.setStyle("height: 100%;");

    this.getItems().addAll(editor, specifications);
  }

  public EditorPane getEditor() {
    return editor;
  }

  public TabPane getSpecifications() {
    return specifications;
  }

  public void setEditor(EditorPane editor) {
    this.editor = editor;
  }

  public void setSpecifications(TabPane specifications) {
    this.specifications = specifications;
  }
}
