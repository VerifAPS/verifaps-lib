package edu.kit.iti.formal.stvs.view.editor;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;
import org.fxmisc.richtext.StyleSpans;
import org.antlr.v4.runtime.Token;

import java.util.Collection;
import java.util.List;

/**
 * Created by csicar on 09.01.17.
 */
public class EditorPaneController implements Controller {
    private EditorPane view;

    public EditorPaneController(Code code, GlobalConfig globalConfig) {

        this.globalConfig = globalConfig;
    }

    public void onCodeChange(Code code) {

    }

    private StyleSpans<Collection<String>> computeSyntaxHighlighting() {
        return null;
    }

    private void onLexedCodeChange(List<Token> tokens){

    }

    private static StyleSpans<Collection<String>> toStyleSpans(List<Token> tokens){
        return null;
    }

    public void setStylesheet(String url) {

    }

    private GlobalConfig globalConfig;

    @Override
    public EditorPane getView() {
        return null;
    }
}
