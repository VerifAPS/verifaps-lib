package edu.kit.iti.formal.automation.ast;


import edu.kit.iti.formal.automation.visitors.Visitor;

public class RepeatStatement extends WhileStatement {

    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}
