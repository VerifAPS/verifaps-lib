package edu.kit.iti.formal.stvs.model.code;

/**
 * Created by philipp on 09.01.17.
 */
public class SourcecodeToken {

    private String text;
    private Type type;

    public SourcecodeToken(String text, Type type) {
        this.text = text;
        this.type = type;
    }

    public Type getType() {
        return type;
    }

    public String getText() {
        return text;
    }

    public enum Type {
        NUMBER,
        STRING,
        KEYWORD,
        COMMENT,
        OTHER
        // TODO: Find out which ones are provided/needed
    }

}
