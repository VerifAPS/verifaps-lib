package edu.kit.iti.formal.stvs.view.editor;

import de.jensd.fx.glyphs.GlyphsDude;
import de.jensd.fx.glyphs.fontawesome.FontAwesomeIcon;
import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.FoldableCodeBlock;
import edu.kit.iti.formal.stvs.model.code.ParsedCode;
import edu.kit.iti.formal.stvs.model.code.SyntaxError;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.application.Platform;
import javafx.beans.value.ObservableValue;
import javafx.concurrent.Task;
import javafx.event.Event;
import javafx.event.EventHandler;
import javafx.scene.control.ContextMenu;
import javafx.scene.control.MenuItem;
import javafx.scene.control.SeparatorMenuItem;
import javafx.scene.input.KeyEvent;
import org.antlr.v4.runtime.Token;
import org.fxmisc.richtext.CodeArea;
import org.fxmisc.richtext.StyleSpans;
import org.fxmisc.richtext.StyleSpansBuilder;

import java.time.Duration;
import java.util.*;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

/**
 * Created by csicar on 09.01.17. Some parts are inspired by examples of the used library:
 * https://github.com/TomasMikula/RichTextFX/blob/a098da6309a0f624052fd1d4d6f5079dd6265fbe/richtextfx-demos/src/main/java/org/fxmisc/richtext/demo/JavaKeywords.java
 *
 * @author Lukas Fritsch
 */
public class EditorPaneController implements Controller {
    private EditorPane view;
    private Code code;
    private GlobalConfig globalConfig;
    private ExecutorService executor;

    /**
     * <p>Creates the controller for the {@link EditorPane}.</p>
     *
     * @param code         the code file to be shown
     * @param globalConfig the global configuration (for font size or style)
     */
    public EditorPaneController(Code code, GlobalConfig globalConfig) {
        this.code = code;
        this.view = new EditorPane(code.getSourcecode(),
                code.syntaxErrorsProperty());
        this.globalConfig = globalConfig;
        this.globalConfig.showLineNumbersProperty()
                .addListener(new ShowLineNumbersListener());
        this.view.getStylesheets()
                .add(EditorPane.class.getResource("st-keywords.css")
                        .toExternalForm());
        this.executor = Executors.newSingleThreadExecutor();
        configureTextArea();
        setupContextMenu();
        handleTextChange(computeHighlighting(code.getSourcecode()));
        this.globalConfig.editorFontSizeProperty().addListener(
                (observable, oldValue, newValue) -> updateFontSize(
                        newValue.intValue()));
        this.globalConfig.editorFontFamilyProperty().addListener(
                (observable, oldValue, newValue) -> updateFontFamily(newValue));
        updateFontFamily(globalConfig.getEditorFontFamily());
        updateFontSize(globalConfig.getEditorFontSize());
        filterAltEvents();
    }

    private void filterAltEvents() {

        EventHandler<KeyEvent> handler = e -> {
            if(e.isAltDown()) {
                Event.fireEvent(this.view, e);
            }
        };
        this.view.getCodeArea().setOnKeyPressed(handler);


    }

    private void updateFontFamily(String fontFamily) {
        view.getCodeArea().setStyle(
                "-fx-font-family: " + fontFamily + ";" + "-fx-font-size: "
                        + globalConfig.editorFontSizeProperty().get() + "pt;");
    }

    private void updateFontSize(int size) {
        view.getCodeArea().setStyle(
                "-fx-font-family: " + globalConfig.editorFontFamilyProperty()
                        .get() + ";" + "-fx-font-size: " + size + "pt;");
    }

    private MenuItem createMenuItem(String name, Runnable action,
            FontAwesomeIcon icon) {
        MenuItem item = createMenuItem(name, action);
        item.setGraphic(GlyphsDude.createIcon(icon));
        return item;
    }

    private MenuItem createMenuItem(String name, Runnable action) {
        MenuItem item = new MenuItem(name);
        item.setOnAction(t -> action.run());
        return item;
    }


    private void setupContextMenu() {
        CodeArea codeArea = view.getCodeArea();

        ContextMenu menu = new ContextMenu();
        menu.getItems().addAll(createMenuItem("Undo", codeArea::undo,
                FontAwesomeIcon.UNDO), createMenuItem("Redo", codeArea::redo),
                new SeparatorMenuItem(),
                createMenuItem("Paste", codeArea::paste, FontAwesomeIcon.PASTE),
                createMenuItem("Copy", codeArea::copy, FontAwesomeIcon.COPY),
                createMenuItem("Cut", codeArea::cut, FontAwesomeIcon.CUT),
                createMenuItem("Select All", codeArea::selectAll));
        this.view.setContextMenu(menu);
    }

    private void configureTextArea() {
        CodeArea codeArea = view.getCodeArea();
        code.sourcecodeProperty().bind(codeArea.textProperty());
        codeArea.richChanges()
                .filter(ch -> !ch.getInserted().equals(ch.getRemoved()))
                .successionEnds(Duration.ofMillis(500))
                .hook(collectionRichTextChange -> codeArea.getUndoManager()
                        .mark()).supplyTask(this::computeHighlightingAsync)
                .awaitLatest(codeArea.richChanges()).filterMap(t -> {
            if (t.isSuccess()) {
                return Optional.of(t.get());
            }
            else {
                t.getFailure().printStackTrace();
                return Optional.empty();
            }
        }).subscribe(this::handleTextChange);
    }

    private Task<StyleSpans<Collection<String>>> computeHighlightingAsync() {
        CodeArea codeArea = view.getCodeArea();
        String sourcecode = codeArea.getText();
        Task<StyleSpans<Collection<String>>> task = new Task<StyleSpans<Collection<String>>>() {
            @Override protected StyleSpans<Collection<String>> call()
                    throws Exception {
                return computeHighlighting(sourcecode);
            }
        };
        executor.execute(task);
        return task;
    }

    private StyleSpans<Collection<String>> computeHighlighting(
            String sourcecode) {
        List<Token> tokens = new ArrayList<>();
        List<SyntaxError> syntaxErrors = new ArrayList<>();

        // Short-circuit setting parsed code properties on code, since we're in another thread.
        ParsedCode.parseCode(sourcecode, newTokens -> {
            tokens.addAll(newTokens);
            Platform.runLater(() -> code.tokensProperty().setAll(newTokens));
        }, synErrs -> {
            syntaxErrors.addAll(synErrs);
            Platform.runLater(
                    () -> code.syntaxErrorsProperty().setAll(synErrs));
        }, parsedCode -> Platform
                .runLater(() -> code.parsedCodeProperty().set(parsedCode)));

        StyleSpansBuilder<Collection<String>> spansBuilder = new StyleSpansBuilder<>();

        if (tokens.isEmpty()) {
            spansBuilder.add(Collections.emptyList(), 0);
            return spansBuilder.create();
        }

        tokens.forEach(token ->
                // replaceAll is a work-around for a bug when ANTLR has a
                // different character count than this CodeArea.
                spansBuilder.add(getStyleClassesFor(token, syntaxErrors),
                        token.getText().replaceAll("\\r", "").length()));
        return spansBuilder.create();
    }

    private Collection<String> getStyleClassesFor(Token token,
            List<SyntaxError> syntaxErrors) {
        // getHightlightingClass(token);
        if (syntaxErrors.stream()
                .anyMatch(syntaxError -> syntaxError.isToken(token))) {
            return Collections.singletonList("syntax-error");
        }
        else {
            return getHightlightingClass(token);
        }
    }

    private List<String> getHightlightingClass(Token token) {
        switch (token.getType()) {
        case IEC61131Lexer.COMMENT:
        case IEC61131Lexer.LINE_COMMENT:
            return listOf("comment");
        case IEC61131Lexer.INTERFACE:
        case IEC61131Lexer.END_INTERFACE:
        case IEC61131Lexer.METHOD:
        case IEC61131Lexer.END_METHOD:
        case IEC61131Lexer.EXTENDS:
        case IEC61131Lexer.IMPLEMENTS:
        case IEC61131Lexer.ELSEIF:
        case IEC61131Lexer.THEN:
        case IEC61131Lexer.OF:
        case IEC61131Lexer.PROGRAM:
        case IEC61131Lexer.END_PROGRAM:
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
        case IEC61131Lexer.ELSE:
            return listOf("keyword");
        case IEC61131Lexer.INT:
        case IEC61131Lexer.SINT:
        case IEC61131Lexer.DINT:
        case IEC61131Lexer.LINT:
        case IEC61131Lexer.UINT:
        case IEC61131Lexer.ULINT:
        case IEC61131Lexer.USINT:
        case IEC61131Lexer.UDINT:
        case IEC61131Lexer.BOOL:
        case IEC61131Lexer.BYTE:
        case IEC61131Lexer.WORD:
        case IEC61131Lexer.LWORD:
        case IEC61131Lexer.DWORD:
            return listOf("type");
        case IEC61131Lexer.INTEGER_LITERAL:
            return listOf("number");

        case IEC61131Lexer.STRING_LITERAL:
        case IEC61131Lexer.REAL_LITERAL:
        case IEC61131Lexer.RETAIN:
        case IEC61131Lexer.F_EDGE:
        case IEC61131Lexer.R_EDGE:
        case IEC61131Lexer.VAR_ACCESS:
        case IEC61131Lexer.VAR_TEMP:
        case IEC61131Lexer.VAR_EXTERNAL:
        case IEC61131Lexer.VAR_CONFIG:
        case IEC61131Lexer.REAL:
        case IEC61131Lexer.LREAL:
            return listOf("unsupported");

        case IEC61131Lexer.VAR:
        case IEC61131Lexer.VAR_INPUT:
        case IEC61131Lexer.VAR_IN_OUT:
        case IEC61131Lexer.VAR_OUTPUT:
        case IEC61131Lexer.CONSTANT:
        case IEC61131Lexer.END_VAR:
            return listOf("vardef");
        case IEC61131Lexer.AND:
        case IEC61131Lexer.NOT:
        case IEC61131Lexer.OR:
        case IEC61131Lexer.MOD:
            return listOf("operation");
        default:
            return listOf();
        }
    }

    private <E> List<E> listOf(E... elements) {
        ArrayList<E> list = new ArrayList<>();
        for (E element : elements) {
            list.add(element);
        }
        return list;
    }

    private void handleTextChange(StyleSpans<Collection<String>> highlighting) {
        view.setStyleSpans(highlighting);
    }

    private void handleParsedCodeFoldingBlocks(
            List<FoldableCodeBlock> foldableCodeBlocks) {

    }

    public Code getCode() {
        return this.code;
    }

    @Override public EditorPane getView() {
        return view;
    }

    private class ShowLineNumbersListener
            implements javafx.beans.value.ChangeListener<Boolean> {
        @Override public void changed(
                ObservableValue<? extends Boolean> observableValue,
                Boolean oldValue, Boolean newValue) {
            view.setShowLineNumbers(newValue);
        }
    }
}
