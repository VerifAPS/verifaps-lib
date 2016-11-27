package edu.kit.iti.formal.automation.st.util;

import edu.kit.iti.formal.automation.st.ast.AssignmentStatement;
import edu.kit.iti.formal.automation.st.ast.SymbolicReference;
import edu.kit.iti.formal.automation.st.visitors.Visitable;

import java.util.HashSet;
import java.util.Set;

/**
 * Created by weigl on 10/07/14.
 */
public class UsageFinder extends AstVisitor {
    private Set<String> writtenReferences = new HashSet<>();
    private Set<String> readedReference = new HashSet<>();

    @Override
    public Object visit(AssignmentStatement assignmentStatement) {
        writtenReferences.add((
                (SymbolicReference)
                        assignmentStatement.getVariable()).getIdentifier());

        assignmentStatement.getExpression().visit(this);
        return null;
    }

    @Override
    public Object visit(SymbolicReference symbolicReference) {
        readedReference.add(symbolicReference.getIdentifier());
        return null;
    }

    public Set<String> getWrittenReferences() {
        return writtenReferences;
    }

    public void setWrittenReferences(Set<String> writtenReferences) {
        this.writtenReferences = writtenReferences;
    }

    public Set<String> getReadedReference() {
        return readedReference;
    }

    public void setReadedReference(Set<String> readedReference) {
        this.readedReference = readedReference;
    }

    public static UsageFinder investigate(Visitable visitable) {
        UsageFinder waf = new UsageFinder();
        visitable.visit(waf);
        return waf;
    }
}
