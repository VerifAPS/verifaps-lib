package edu.kit.iti.formal.automation.datatypes.values;

import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.automation.st.ast.Initialization;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 24.11.16.
 */
public class PointerValue extends Initialization {
    @Override
    public Any dataType(LocalScope localScope) throws VariableNotDefinedException, TypeConformityException {
        return null;
    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return null;
    }
}
