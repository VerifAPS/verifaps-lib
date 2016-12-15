package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 13.06.14.
 */
public abstract class TypeDeclaration<T extends Initialization> extends Top {
    protected String typeName;
    protected String baseTypeName;
    protected Any baseType;
    protected T initializationValue;
    private T initialization;

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

    public void setInitialization(T initialization) {
        this.initialization = initialization;
    }


    public Any getBaseType() {
        return baseType;
    }

    public void setBaseType(Any baseType) {
        this.baseType = baseType;
    }

    public T getInitialization() {
        return initialization;
    }

    public Any getDataType(GlobalScope globalScope) {
        setBaseType(globalScope.resolveDataType(getBaseTypeName()));
        return getBaseType();
    }

}
