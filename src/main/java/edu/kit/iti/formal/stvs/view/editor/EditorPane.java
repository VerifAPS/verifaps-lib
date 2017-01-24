package edu.kit.iti.formal.stvs.view.editor;

import javafx.beans.property.StringProperty;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.StackPane;
import javafx.scene.layout.VBox;
import org.fxmisc.richtext.CodeArea;
import org.fxmisc.richtext.LineNumberFactory;
import org.fxmisc.richtext.StyleSpans;

import java.time.Duration;
import java.util.Collection;
import java.util.Optional;

/**
 * Created by csicar on 09.01.17.
 */
public class EditorPane extends StackPane {

  /**
   * Contains ButtonList and CodeArea
   */
  private HBox horizontalBox;
  private CodeArea codeArea;
  private VBox buttonList;

  public EditorPane(String code) {
    super();
    codeArea = new CodeArea(code);
    codeArea.setParagraphGraphicFactory(LineNumberFactory.get(codeArea));
    super.getChildren().addAll(codeArea);
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
    codeArea.setStyleSpans(0, style);
  }

  public CodeArea getCodeArea() {
    return codeArea;
  }

  public VBox getButtonList() {
    return buttonList;
  }
}
