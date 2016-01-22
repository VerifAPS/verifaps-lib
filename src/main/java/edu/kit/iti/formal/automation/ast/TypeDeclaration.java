package edu.kit.iti.formal.automation.ast;

import edu.kit.iti.formal.automation.visitors.Visitor;
import edu.kit.iti.formal.automation.visitors.Visitable;

/**
 * Created by weigl on 13.06.14.
 */
public abstract class TypeDeclaration<T> implements Visitable {
    protected String typeName;
    protected String baseTypeName;
    protected T initializationValue;

    public TypeDeclaration() {
    }

    public TypeDeclaration(String typeName) {
        this.typeName = typeName;
    }

    public String getTypeName() {
        if (typeName == null) return baseTypeName;
        return typeName;
    }

    public void setTypeName(String typeName) {
        this.typeName = typeName;
    }

    public String getBaseTypeName() {
        return baseTypeName;
    }

    public void setBaseTypeName(String baseTypeName) {
        this.baseTypeName = baseTypeName;
    }

    public T getInitializationValue() {
        return initializationValue;
    }

    public void setInitializationValue(T initializationValue) {
        this.initializationValue = initializationValue;
    }

    public abstract <S> S visit(Visitor<S> visitor);

}
