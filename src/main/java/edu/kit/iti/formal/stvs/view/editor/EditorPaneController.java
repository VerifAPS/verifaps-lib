package edu.kit.iti.formal.stvs.view.editor;

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
