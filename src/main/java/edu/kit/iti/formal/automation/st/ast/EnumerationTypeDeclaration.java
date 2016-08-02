package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.datatypes.EnumerateType;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.LinkedList;
import java.util.List;

/**
 * Created by weigl on 13.06.14.
 */
public class EnumerationTypeDeclaration extends TypeDeclaration<String> {
    private List<String> allowedValues = new LinkedList<>();

    public EnumerationTypeDeclaration() {
        setBaseTypeName("ENUM");
    }

    @Override
    public <S> S visit(Visitor<S> visitor) {
        return visitor.visit(this);
    }

    public void addValue(String text) {
        allowedValues.add(text);
    }

    public List<String> getAllowedValues() {
        return allowedValues;
    }

    public void setAllowedValues(List<String> allowedValues) {
        this.allowedValues = allowedValues;
    }

    public EnumerateType toDataType() {
        String[] aV = allowedValues.toArray(new String[0]);

        String init = initializationValue != null ? initializationValue : aV[0];

        EnumerateType et = new EnumerateType(getTypeName(), aV, init);
        return et;
    }

}
