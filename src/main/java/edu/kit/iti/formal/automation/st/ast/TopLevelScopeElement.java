package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.GlobalScope;
import edu.kit.iti.formal.automation.LocalScope;

/**
 * Created by weigl on 13.06.14.
 */
public abstract class TopLevelScopeElement extends TopLevelElement {
    private LocalScope localScope = new LocalScope();

    protected TopLevelScopeElement() {

    }

    public void setGlobalScope(GlobalScope global) {
        localScope.setGlobalScope(global);
    }

    public TopLevelScopeElement(TopLevelScopeElement p) {
        localScope = new LocalScope(p.getLocalScope());
    }

    public LocalScope getLocalScope() {
        return localScope;
    }

    public void setLocalScope(LocalScope localScope) {
        this.localScope = localScope;
    }


}
