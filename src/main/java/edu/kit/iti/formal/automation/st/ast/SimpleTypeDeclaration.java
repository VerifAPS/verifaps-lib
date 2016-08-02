package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 13.06.14.
 */
public class SimpleTypeDeclaration extends TypeDeclaration<ScalarValue<?, ?>> {
    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}
