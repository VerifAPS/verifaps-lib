package edu.kit.iti.formal.stvs.view.spec.table;

import javafx.scene.control.TextField;
import javafx.scene.text.Text;

public class CommentPopup extends javafx.stage.Popup {
    private static Text commentHeadline;
    private TextField commentField;

    public TextField getCommentField() {
        return commentField;
    }
}
