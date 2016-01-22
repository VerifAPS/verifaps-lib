package edu.kit.iti.formal.automation.ast;

import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 13.06.14.
 */
public class ResourceDeclaration extends TopLevelScopeElement {

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String getBlockName() {
        return "<resource>";
    }
}
