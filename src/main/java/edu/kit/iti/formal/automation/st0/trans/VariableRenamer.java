package edu.kit.iti.formal.automation.st0.trans;

import edu.kit.iti.formal.automation.st.ast.StatementList;
import edu.kit.iti.formal.automation.st.ast.SymbolicReference;
import edu.kit.iti.formal.automation.st.util.AstCopyVisitor;

import java.util.function.Function;

/**
 * @author weigla
 * @date 26.06.2014
 */
public class VariableRenamer extends AstCopyVisitor {
    private final StatementList statements;
    private final Function<String, String> newName;

    public VariableRenamer(StatementList functionBody, Function<String, String> newName) {
        this.newName = newName;
        statements = functionBody;
    }

    @Override
    public Object visit(SymbolicReference symbolicReference) {
        String name = newName.apply(symbolicReference.getIdentifier());
        SymbolicReference ref = new SymbolicReference(name, symbolicReference.getSub());
        ref.setSubscripts(symbolicReference.getSubscripts());
        return ref;
    }

    public StatementList rename() {
        return (StatementList) statements.visit(this);
    }
}
