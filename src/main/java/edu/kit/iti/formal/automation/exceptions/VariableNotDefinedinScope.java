package edu.kit.iti.formal.automation.exceptions;

import edu.kit.iti.formal.automation.LocalScope;
import edu.kit.iti.formal.automation.st.ast.SymbolicReference;

/**
 * Created by weigl on 24.11.16.
 */
public class VariableNotDefinedinScope extends Exception {
    private final SymbolicReference reference;
    private final LocalScope localScope;

    public VariableNotDefinedinScope(LocalScope variableDeclarations, SymbolicReference reference) {
        this.localScope = variableDeclarations;
        this.reference = reference;
    }

    public SymbolicReference getReference() {
        return reference;
    }

    public LocalScope getLocalScope() {
        return localScope;
    }

    @Override
    public String getMessage() {
        return "Variable: " + reference.getIdentifier() + " not defined in the given localScope " + localScope;
    }
}
