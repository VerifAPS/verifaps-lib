package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 02.08.16.
 */
public class Deref extends Reference {
    private Reference reference;

    public Deref(Reference reference) {
        this.reference = reference;
    }

    public Reference getReference() {
        return reference;
    }

    public void setReference(Reference reference) {
        this.reference = reference;
    }

    @Override
    public String toString() {
        return reference + "^";
    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}
