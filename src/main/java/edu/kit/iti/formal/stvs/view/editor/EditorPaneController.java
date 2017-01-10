package edu.kit.iti.formal.stvs.view.editor;

import edu.kit.iti.formal.stvs.model.code.Code;
import org.fxmisc.richtext.StyleSpans;

/**
 * Created by csicar on 09.01.17.
 */
public class EditorPaneController implements OnCodeModelChangeListener {
    public EditorPaneController(Code code) {

        // code.addChangeListener(this);
    };
    public void onCodeChange(Code code) {

    };
    private StyleSpans computeSyntaxHighlighting(){
        return null;
    };
}
