package edu.kit.iti.formal.automation.ast;

import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 13.06.14.
 */
public class ConfigurationDeclaration extends TopLevelScopeElement {

    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String getBlockName() {
        return "<configuration>";
    }
}
