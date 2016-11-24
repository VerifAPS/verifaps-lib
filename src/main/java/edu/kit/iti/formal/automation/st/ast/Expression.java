package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.datatypes.Any;

public abstract class Expression extends Top {
    public abstract Any dataType(VariableScope scope);
}
