package edu.kit.iti.formal.automation.ast;

/**
 * Created by weigl on 13.06.14.
 */
public abstract class TopLevelScopeElement extends TopLevelElement {
    private VariableScope scope = new VariableScope();

    protected TopLevelScopeElement() {
    }

    public TopLevelScopeElement(TopLevelScopeElement p) {
        scope = new VariableScope(p.getScope());
    }

    public VariableScope getScope() {
        return scope;
    }

    public void setScope(VariableScope scope) {
        this.scope = scope;
    }


}
