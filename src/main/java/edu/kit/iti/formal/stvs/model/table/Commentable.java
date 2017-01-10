package edu.kit.iti.formal.stvs.model.table;

import java.util.function.Consumer;

public interface Commentable {
    public void setComment(String comment);
    public String getComment();
    public void addCommentListener(Consumer<Commentable>);
}
