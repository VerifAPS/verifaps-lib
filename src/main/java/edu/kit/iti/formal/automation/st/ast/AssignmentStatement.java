package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 11.06.14.
 */
public class AssignmentStatement extends Statement {
    private Reference variable;
    private Expression expression;

    public AssignmentStatement() {
    }

    public AssignmentStatement(Reference variable, Expression expression) {
        this.variable = variable;
        this.expression = expression;
    }


    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    public Reference getLocation() {
        return variable;
    }

    public void setLocation(Reference variable) {
        this.variable = variable;
    }

    public Expression getExpression() {
        return expression;
    }

    public void setExpression(Expression expression) {
        this.expression = expression;
    }
}
