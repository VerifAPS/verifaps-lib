package edu.kit.iti.formal.automation.ast;


import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigla on 09.06.2014.
 */
@Deprecated
public class Literal extends Expression {
    LiteralType type;
    String cast;
    String literal;
    Object value;

    public Literal() {
    }

    public Literal(LiteralType type, String cast, String literal, Object value) {
        this.type = type;
        this.cast = cast;
        this.literal = literal;
        this.value = value;
    }

    public LiteralType getType() {
        return type;
    }

    public void setType(LiteralType type) {
        this.type = type;
    }

    public String getCast() {
        return cast;
    }

    public void setCast(String cast) {
        this.cast = cast;
    }

    public String getLiteral() {
        return literal;
    }

    public void setLiteral(String literal) {
        this.literal = literal;
    }

    public Object getValue() {
        return value;
    }

    public void setValue(Object value) {
        this.value = value;
    }

    public static enum LiteralType {
        LREAL, REAL, STRING, WSTRING,
        SINT, UINT, BINARY, OCTAL, HEX,
        DURATION, TIME_OF_DAY, BIT_STRING, BOOLEAN;
    }


    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}
