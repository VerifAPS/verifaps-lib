package edu.kit.iti.formal.stvs.view.editor;

import edu.kit.iti.formal.stvs.model.code.Code;

/**
 * Created by csicar on 09.01.17.
 */
public class EditorPaneController implements OnCodeModelChangeListener {
    public EditorPaneController(CodeModel codeModel) {
        codeModel.setOnCodeChangeListener(this);
    };
    public void onCodeChange(Code code) {

    };
    private StyleSpans computeSyntaxHighlighting(){
        return null;
    };
}
