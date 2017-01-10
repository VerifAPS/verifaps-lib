package edu.kit.iti.formal.stvs.view.spec.table;

import javafx.beans.property.StringProperty;

public class CommentPopupController {
    private boolean editable;
    private StringProperty comment;

    public CommentPopupController(Commentable commentable, boolean editable) {
    }

    public StringProperty getCommentProperty() {
        return comment;
    }
}
