package edu.kit.iti.formal.automation.datatypes;

/**
 * Created by weigl on 10.06.14.
 */
public abstract class Any {
    protected String name = "any";

    protected Any() {
        name = getClass().getSimpleName().toUpperCase();
    }

    protected Any(String name) {
        this.name = name;
    }

    protected void setName(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    public abstract String repr(Object obj);
}
