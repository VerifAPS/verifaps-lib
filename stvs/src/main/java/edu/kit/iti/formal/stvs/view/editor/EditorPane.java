package edu.kit.iti.formal.stvs.view.editor;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.formal.stvs.model.code.SyntaxError;
import edu.kit.iti.formal.stvs.view.ViewUtils;

import java.util.Collection;
import java.util.function.IntFunction;
import java.util.logging.Filter;
import java.util.stream.Collector;

import javafx.application.Platform;
import javafx.beans.property.StringProperty;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.collections.transformation.FilteredList;
import javafx.geometry.Orientation;
import javafx.scene.Node;
import javafx.scene.control.Label;
import javafx.scene.control.ListView;
import javafx.scene.control.SplitPane;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.text.Text;
import org.controlsfx.control.PopOver;
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

  private final IntFunction<Node> lineNumberFactory;
  private final ObservableList<SyntaxError> syntaxErrors;

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
    this.syntaxErrors = syntaxErrors;
    ViewUtils.setupView(this);

    codeArea = new CodeArea(code);
    lineNumberFactory = LineNumberFactory.get(codeArea);
    if (showLineNumbers) {
      codeArea.setParagraphGraphicFactory(this::createLinePrefixForLine);
    }
    this.getItems().addAll(codeArea);
    this.setOrientation(Orientation.VERTICAL);
    this.setDividerPositions(0.8);
  }

  private void setLineIcon(int i, FilteredList<SyntaxError> syntaxErrors, Label icon) {
    icon.setVisible(syntaxErrors.size() != 0);
    String combinedMessages = syntaxErrors.stream()
        .map(SyntaxError::getMessage)
        .reduce("", (s, s2) -> s + s2);
    icon.setTooltip(new Tooltip(combinedMessages));
  }

  /**
   * prefix the line with the line number and possibly an error icon
   * @param i line number
   * @return Node intended as the prefix
   */
  private Node createLinePrefixForLine(int i) {

    Label icon = GlyphsDude.createIconLabel(FontAwesomeIcon.EXCLAMATION_CIRCLE, "", null, null, null);
    FilteredList<SyntaxError> lineSyntaxErrors = syntaxErrors.filtered(syntaxError -> syntaxError.getLine() == i + 1);
    setLineIcon(i, lineSyntaxErrors, icon);
    syntaxErrors.addListener((ListChangeListener.Change<?> change) -> {
      setLineIcon(i, lineSyntaxErrors, icon);
    });
    return new HBox(lineNumberFactory.apply(i), icon);
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
   * <p>Sett for showing line numbers.</p>
   *
   * @param showLineNumbers whether to show line numbers in the {@link CodeArea}.
   */
  public void setShowLineNumbers(boolean showLineNumbers) {
    if (showLineNumbers) {
      codeArea.setParagraphGraphicFactory(this::createLinePrefixForLine);
    } else {
      codeArea.setParagraphGraphicFactory(null);
    }
  }
}
