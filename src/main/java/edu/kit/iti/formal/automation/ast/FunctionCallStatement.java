package edu.kit.iti.formal.automation.ast;

import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 11.06.14.
 */
public class FunctionCallStatement extends Statement {
    private FunctionCall functionCall;

    public FunctionCallStatement(FunctionCall fc) {
        this.functionCall = fc;
    }

    public FunctionCall getFunctionCall() {
        return functionCall;
    }

    public void setFunctionCall(FunctionCall functionCall) {
        this.functionCall = functionCall;
    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}
