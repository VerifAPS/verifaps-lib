package edu.kit.iti.formal.stvs.view.editor;

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.FoldableCodeBlock;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.concurrent.Task;
import org.antlr.v4.runtime.Token;
import org.fxmisc.richtext.CodeArea;
import org.fxmisc.richtext.StyleSpans;
import org.fxmisc.richtext.StyleSpansBuilder;

import java.time.Duration;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

/**
 * Created by csicar on 09.01.17.
 * <p>
 * Some parts are inspired by examples of the used library:
 * https://github.com/TomasMikula/RichTextFX/blob/a098da6309a0f624052fd1d4d6f5079dd6265fbe/richtextfx-demos/src/main/java/org/fxmisc/richtext/demo/JavaKeywords.java
 */
public class EditorPaneController implements Controller {
  private EditorPane view;
  private Code code;
  private GlobalConfig globalConfig;
  private ExecutorService executor;

  public EditorPaneController(Code code, GlobalConfig globalConfig) {
    this.code = code;
    this.view = new EditorPane(code.sourcecodeProperty().get());
    this.globalConfig = globalConfig;

    this.view.getStylesheets().add(EditorPane.class.getResource("st-keywords.css").toExternalForm());
    this.executor = Executors.newSingleThreadExecutor();
    configureSyntaxHighlighting();
    applyHighlighting(computeHighlighting(code.sourcecodeProperty().get()));
  }

  private void configureSyntaxHighlighting() {
    CodeArea codeArea = view.getCodeArea();
    codeArea.richChanges()
        .filter(ch -> !ch.getInserted().equals(ch.getRemoved()))
        .successionEnds(Duration.ofMillis(500))
        .hook(collectionRichTextChange -> codeArea.getUndoManager().mark())
        .supplyTask(this::computeHighlightingAsync)
        .awaitLatest(codeArea.richChanges())
        .filterMap(t -> {
          if(t.isSuccess()) {
            return Optional.of(t.get());
          } else {
            t.getFailure().printStackTrace();
            return Optional.empty();
          }
        })
        .subscribe(this::applyHighlighting);
  }

  private Task<StyleSpans<Collection<String>>> computeHighlightingAsync() {
    CodeArea codeArea = view.getCodeArea();
    String sourcecode = codeArea.getText();
    Task<StyleSpans<Collection<String>>> task = new Task<StyleSpans<Collection<String>>>() {
      @Override
      protected StyleSpans<Collection<String>> call() throws Exception {
        return computeHighlighting(sourcecode);
      }
    };
    executor.execute(task);
    return task;
  }

  private StyleSpans<Collection<String>> computeHighlighting(String sourcecode) {
    List<? extends Token> tokens = code.computeTokens(sourcecode);

    StyleSpansBuilder<Collection<String>> spansBuilder
        = new StyleSpansBuilder<>();

    tokens.forEach(token ->
      spansBuilder.add(getStyleClassesFor(token), token.getText().replaceAll("\\r", "").length())
    );
    return spansBuilder.create();
  }

  private Collection<String> getStyleClassesFor(Token token) {
    System.out.print(token.getText());
    // TODO: Add more colours (styles) to tokens
    switch (token.getType()) {
      case IEC61131Lexer.TYPE:
      case IEC61131Lexer.END_TYPE:
      case IEC61131Lexer.IF:
      case IEC61131Lexer.END_IF:
      case IEC61131Lexer.FUNCTION:
      case IEC61131Lexer.END_FUNCTION:
      case IEC61131Lexer.FUNCTION_BLOCK:
      case IEC61131Lexer.END_FUNCTION_BLOCK:
      case IEC61131Lexer.CASE:
      case IEC61131Lexer.END_CASE:
        return Collections.singleton("keyword");
      case IEC61131Lexer.INTEGER_LITERAL:
        return Collections.singleton("number");
      case IEC61131Lexer.STRING_LITERAL:
        return Collections.singleton("string");
      case IEC61131Lexer.VAR:
      case IEC61131Lexer.VAR_INPUT:
      case IEC61131Lexer.VAR_IN_OUT:
      case IEC61131Lexer.VAR_OUTPUT:
      case IEC61131Lexer.END_VAR:
        return Collections.singleton("vardef");
      default:
        return Collections.emptyList();
    }
  }

  private void applyHighlighting(StyleSpans<Collection<String>> highlighting) {
    view.setStyleSpans(highlighting);
  }

  private void handleParsedCodeFoldingBlocks(List<FoldableCodeBlock> foldableCodeBlocks) {

  }

  // TODO: Implement this?
  public void setStylesheet(String url) {
  }

  @Override
  public EditorPane getView() {
    return view;
  }
}
