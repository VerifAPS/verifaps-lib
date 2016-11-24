package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 11.06.14.
 */
public class DirectVariable extends Reference {
    public DirectVariable(String s) {

    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        throw new IllegalStateException("not implemented");
    }

    @Override
    public Any dataType(VariableScope scope) {
        throw new IllegalStateException(("not implemented"));
    }
}
