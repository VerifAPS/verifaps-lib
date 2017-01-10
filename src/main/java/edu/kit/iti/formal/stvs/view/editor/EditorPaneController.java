package edu.kit.iti.formal.stvs.view.editor;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.SourcecodeToken;
import edu.kit.iti.formal.stvs.view.Controller;
import org.fxmisc.richtext.StyleSpans;

import java.util.Collection;
import java.util.List;

/**
 * Created by csicar on 09.01.17.
 */
public class EditorPaneController implements Controller {
    private EditorPane view;

    public EditorPaneController(Code code) {

    }

    public void onCodeChange(Code code) {

    }

    private StyleSpans<Collection<String>> computeSyntaxHighlighting() {
        return null;
    }

    private void onLexedCodeChange(List<SourcecodeToken> tokens){

    }

    private static StyleSpans<Collection<String>> toStyleSpans(List<SourcecodeToken> tokens){
        return null;
    }

    public void setStylesheet(String url) {

    }

    @Override
    public EditorPane getView() {
        return null;
    }
}
