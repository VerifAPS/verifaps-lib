package edu.kit.iti.formal.automation.ast;


import edu.kit.iti.formal.automation.visitors.Visitor;
import edu.kit.iti.formal.automation.visitors.Visitable;

/**
 * Created by weigla on 09.06.2014.
 */
@Deprecated
public class Constant implements Visitable {
    private Literal literal;

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}
