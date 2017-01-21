package edu.kit.iti.formal.stvs.view.editor;

import javafx.beans.property.StringProperty;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;
import org.fxmisc.richtext.CodeArea;
import org.fxmisc.richtext.StyleSpans;

import java.util.Collection;

/**
 * Created by csicar on 09.01.17.
 */
public class EditorPane extends Pane {

  /**
   * Contains ButtonList and CodeArea
   */
  private HBox horizontalBox;
  private CodeArea codeArea;
  private VBox buttonList;

  public EditorPane(String code) {
    codeArea = new CodeArea(code);
  }


  public StringProperty getCodeProperty() {
    return null;
  }

  public String getCode() {
    return this.codeArea.getText();
  }

  public void setCode(String code) {
    codeArea = new CodeArea(code);
  }


  public void setStyleSpans(StyleSpans<Collection<String>> style) {
  }

  public CodeArea getCodeArea() {
    return codeArea;
  }

  public VBox getButtonList() {
    return buttonList;
  }
}
