package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.table.Commentable;
import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.property.StringProperty;
import javafx.scene.layout.Pane;

public class CommentPopupController implements Controller {
    private boolean editable;
    private StringProperty comment;
    private GlobalConfig globalConfig;

    public CommentPopupController(Commentable commentable, boolean editable, GlobalConfig globalConfig) {
        this.globalConfig = globalConfig;
    }

    public StringProperty getCommentProperty() {
        return comment;
    }

    @Override
    //Pane is not the right type here. We will need to change this
    public Pane getView() {
        return null;
    }
}
