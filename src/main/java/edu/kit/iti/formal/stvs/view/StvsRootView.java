package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.view.editor.EditorPane;
import edu.kit.iti.formal.stvs.view.menu.StvsMenuBar;
import javafx.scene.control.TabPane;
import javafx.scene.layout.Pane;

/**
 * Created by csicar on 09.01.17.
 */
public class StvsRootView extends Pane {
  private StvsMenuBar menuBar;
  private EditorPane editor;
  private TabPane specifications;

  public StvsMenuBar getMenuBar() {
    return menuBar;
  }

  public EditorPane getEditor() {
    return editor;
  }

  public TabPane getSpecifications() {
    return specifications;
  }

  public void setMenuBar(StvsMenuBar menuBar) {
    this.menuBar = menuBar;
  }

  public void setEditor(EditorPane editor) {
    this.editor = editor;
  }

  public void setSpecifications(TabPane specifications) {
    this.specifications = specifications;
  }
}
