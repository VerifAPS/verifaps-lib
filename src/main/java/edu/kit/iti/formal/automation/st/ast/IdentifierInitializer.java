package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.EnumerateType;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * @author Alexander Weigl
 * @version 1 (16.12.16)
 */
public class IdentifierInitializer extends Initialization {
    private EnumerateType enumType;
    private String value;

    public IdentifierInitializer() {
    }

    public IdentifierInitializer(String value) {
        this.value = value;
    }

    public EnumerateType getEnumType() {
        return enumType;
    }

    public IdentifierInitializer setEnumType(EnumerateType enumType) {
        this.enumType = enumType;
        return this;
    }

    public String getValue() {
        return value;
    }

    public IdentifierInitializer setValue(String value) {
        this.value = value;
        return this;
    }

    @Override
    public Any dataType(LocalScope localScope) throws VariableNotDefinedException, TypeConformityException {
        return enumType;
    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}
