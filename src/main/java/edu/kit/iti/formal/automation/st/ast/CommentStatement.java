package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * @author weigla
 * @date 24.06.2014
 */
public class CommentStatement extends Statement {
    public String comment;

    public CommentStatement() {
    }

    public CommentStatement(String format, Object... args) {
        this(String.format(format, args));
    }

    public CommentStatement(String comment) {
        this.comment = comment;
    }

    public String getComment() {
        return comment;
    }

    public void setComment(String comment) {
        this.comment = comment;
    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}
