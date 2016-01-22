package edu.kit.iti.formal.automation.ast;

import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigla on 09.06.2014.
 */
public class WhileStatement extends GuardedStatement {
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}
