package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;

/**
 * Created by philipp on 09.01.17.
 */
public class IOVariable {

    public enum Category {
        INPUT,
        OUTPUT
    }

    private Category category;
    private Type type;

    public IOVariable(Category category, Type type) {
        this.category = category;
        this.type = type;
    }

    public Category getCategory() {
        return category;
    }

    public Type getType() {
        return type;
    }

    public void setType(Type type) {

    }

}
