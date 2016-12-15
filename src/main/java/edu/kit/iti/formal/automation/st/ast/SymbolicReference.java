package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 11.06.14.
 */
public class SymbolicReference extends Reference {
    private String identifier;
    private ExpressionList subscripts;
    private Reference sub;


    public SymbolicReference(String s, Reference sub) {
        this.sub = sub;
        identifier = s;
    }

    public SymbolicReference(String s) {
        this(s, null);
    }

    public SymbolicReference(SymbolicReference symbolicReference) {
        this.identifier = symbolicReference.identifier;
        this.subscripts = symbolicReference.getSubscripts();
        this.sub = symbolicReference.sub;
    }

    public SymbolicReference() {

    }

    public void addSubscript(Expression ast) {
        subscripts.add(ast);
    }

    public String getIdentifier() {
        return identifier;
    }

    public void setIdentifier(String identifier) {
        this.identifier = identifier;
    }

    public ExpressionList getSubscripts() {
        return subscripts;
    }

    public void setSubscripts(ExpressionList subscripts) {
        this.subscripts = subscripts;
    }

    public Reference getSub() {
        return sub;
    }

    public void setSub(Reference sub) {
        this.sub = sub;
    }


    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof SymbolicReference)) return false;

        SymbolicReference that = (SymbolicReference) o;

        if (!identifier.equals(that.identifier)) return false;
        if (sub != null ? !sub.equals(that.sub) : that.sub != null) return false;
        if (subscripts != null ? !subscripts.equals(that.subscripts) : that.subscripts != null) return false;

        return true;
    }

    @Override
    public int hashCode() {
        int result = identifier.hashCode();
        result = 31 * result + (subscripts != null ? subscripts.hashCode() : 0);
        result = 31 * result + (sub != null ? sub.hashCode() : 0);
        return result;
    }

    public void derefVar() {
    }

    public void derefSubscript() {

    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public Any dataType(LocalScope localScope) throws VariableNotDefinedException {
        return localScope.getVariable(this).getDataType();
    }
}
