package edu.kit.iti.formal.stvs.view.editor;

import edu.kit.iti.formal.stvs.model.code.SyntaxError;
import edu.kit.iti.formal.stvs.view.ViewUtils;

import java.util.Collection;

import javafx.beans.property.StringProperty;
import javafx.collections.ObservableList;
import javafx.geometry.Orientation;
import javafx.scene.control.ListView;
import javafx.scene.control.SplitPane;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.Pane;
import org.fxmisc.richtext.CodeArea;
import org.fxmisc.richtext.LineNumberFactory;
import org.fxmisc.richtext.StyleSpans;

/**
 * <p>
 * The view for the left side of our application: The code editor.
 * </p>
 *
 * <p>
 * This view contains both the {@link CodeArea} for editing the code and the {@link ListView} for
 * viewing a list of syntax errors. It itself extends a {@link SplitPane} for combining these two
 * views.
 * </p>
 *
 * <p>
 * Created by csicar on 09.01.17.
 * </p>
 *
 * @author Lukas Fritsch
 */
public class EditorPane extends SplitPane {

  private CodeArea codeArea;
  private ListView<SyntaxError> syntaxErrorListView;

  private Pane syntaxErrorPane;

  /**
   * <p>
   * Creates an EditorPane with the given code as initial source code text.
   * </p>
   *
   * <p>
   * This is a default constructor (see {@link #EditorPane(String, ObservableList, boolean)}) for
   * initializing showing of lines to true
   * </p>
   *
   * @param code the string to initialize the {@link CodeArea} to
   * @param syntaxErrors the initial list of {@link SyntaxError}s.
   */
  public EditorPane(String code, ObservableList<SyntaxError> syntaxErrors) {
    this(code, syntaxErrors, true);
  }

  /**
   * <p>
   * Creates an editable EditorPane with the given code as initial source code text.
   * </p>
   *
   * @param code the string to initialize the {@link CodeArea} to
   * @param syntaxErrors the initial list of {@link SyntaxError}s.
   * @param showLineNumbers whether to show line numbers in the {@link CodeArea}
   */
  public EditorPane(String code, ObservableList<SyntaxError> syntaxErrors,
      boolean showLineNumbers) {
    super();
    ViewUtils.setupView(this);

    codeArea = new CodeArea(code);
    if (showLineNumbers) {
      codeArea.setParagraphGraphicFactory(LineNumberFactory.get(codeArea));
    }
    syntaxErrorListView = new ListView<>(syntaxErrors);
    syntaxErrorListView.getStyleClass().addAll("model-text-area");
    syntaxErrorPane = new AnchorPane(syntaxErrorListView);
    AnchorPane.setBottomAnchor(syntaxErrorListView, 0.0);
    AnchorPane.setTopAnchor(syntaxErrorListView, 0.0);
    AnchorPane.setLeftAnchor(syntaxErrorListView, 0.0);
    AnchorPane.setRightAnchor(syntaxErrorListView, 0.0);
    this.getItems().addAll(codeArea, syntaxErrorPane);
    this.setOrientation(Orientation.VERTICAL);
    this.setDividerPositions(0.8);
  }

  public ListView<SyntaxError> getSyntaxErrorListView() {
    return syntaxErrorListView;
  }

  public Pane getSyntaxErrorPane() {
    return syntaxErrorPane;
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

  /**
   * shows / hides linenumbers (as in the global config specified)
   *
   * @param showLineNumbers line numbers to show or not
   */
  public void setShowLineNumbers(Boolean showLineNumbers) {
    if (showLineNumbers) {
      codeArea.setParagraphGraphicFactory(LineNumberFactory.get(codeArea));
    } else {
      codeArea.setParagraphGraphicFactory(null);
    }
  }
}
