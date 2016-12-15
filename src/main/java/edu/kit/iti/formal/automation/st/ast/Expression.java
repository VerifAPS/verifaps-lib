package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;

public abstract class Expression extends Top {
    public abstract Any dataType(LocalScope localScope)
            throws VariableNotDefinedException,
            TypeConformityException;
}
