package edu.kit.iti.formal.automation.analysis;

import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import lombok.RequiredArgsConstructor;

@RequiredArgsConstructor
public class CheckForTypes extends AstVisitor<Void> {
    private final Reporter reporter;
    private Scope scope;

    @Override
    public Void visit(SymbolicReference symbolicReference) {
        if (null == scope.getVariable(symbolicReference.getIdentifier()))
            reporter.report(
                    symbolicReference.getStartPosition(),
                    "Could not find variable "+symbolicReference.getIdentifier()+".",
                    "var-resolve", "error");
        return null;    //super.visit(symbolicReference)
    }

    @Override
    public Void visit(FunctionDeclaration functionDeclaration) {
        if (null == functionDeclaration.getReturnType()) {
            reporter.report(functionDeclaration.getStartPosition(),
                    "Return type " + functionDeclaration.getReturnTypeName() + " not found.",
                    "type-resolve", "error");
        }
        super.visit(functionDeclaration);
        return null;
    }

    @Override
    public Void visit(Scope localScope) {
        scope = localScope;
        super.visit(localScope);
        return null;
    }

    @Override
    public Void visit(InvocationStatement invocation) {
        invocation.getCallee().accept(this);

        return null;
    }

    @Override
    public Void visit(Invocation invocation) {
        invocation.getCallee().accept(this);
        return null;
    }

    public interface Reporter {
        void report(Position position, String msg, String category, String error);
    }
}
