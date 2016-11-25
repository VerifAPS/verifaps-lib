package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.datatypes.PointerType;
import edu.kit.iti.formal.automation.datatypes.values.PointerValue;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 24.11.16.
 * // TODO: 24.11.16  create everything
 */
public class PointerTypeDeclaration
        extends TypeDeclaration<ScalarValue<PointerType, PointerValue>> {

    public PointerTypeDeclaration(String pointsTo) {

    }

    @Override
    public <S> S visit(Visitor<S> visitor) {
        return visitor.visit(this);
    }
}
