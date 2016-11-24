package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.LocalScope;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedinScope;

public abstract class Expression extends Top {
    public abstract Any dataType(LocalScope localScope)
            throws VariableNotDefinedinScope,
            TypeConformityException;
}
