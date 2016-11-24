package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 02.08.16.
 */
public class Location extends Expression {
    List<Reference> path = new ArrayList<>(5);

    public Location() {
    }

    public Location(List<Reference> path) {
        this.path = path;
    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    public void add(Reference ast) {
        path.add(ast);
    }

    public void lastDeref() {
        Deref deref = new Deref(path.get(path.size() - 1));
        path.remove(path.size() - 1);
        path.add(deref);
    }

    public String asIdentifier() {
        return path.stream().map(a -> a.toString()).reduce("", (a, b) -> a + "." + b);
    }

    @Override
    public Any dataType(VariableScope scope) {
        return null;//TODO
    }
}
