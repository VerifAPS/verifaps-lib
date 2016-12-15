package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.ValueFactory;
import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.*;

/**
 * Created by weigl on 13.06.14.
 */
public class EnumerationTypeDeclaration extends TypeDeclaration<ScalarValue<EnumerateType, ?>> {
    private List<String> allowedValues = new LinkedList<>();
    private Map<String, ScalarValue<? extends AnyInt, Long>> values = new HashMap<>();
    private int counter = 0;

    public EnumerationTypeDeclaration() {
        setBaseTypeName("ENUM");
    }

    @Override
    public <S> S visit(Visitor<S> visitor) {
        return visitor.visit(this);
    }

    public void addValue(String text) {
        allowedValues.add(text);
        values.put(text, ValueFactory.makeUInt(counter));
        counter++;
    }

    public List<String> getAllowedValues() {
        return allowedValues;
    }

    public void setAllowedValues(List<String> allowedValues) {
        this.allowedValues = allowedValues;
    }

    @Override
    public EnumerateType getDataType(GlobalScope globalScope) {
        String init = allowedValues.get(0);
        if (initializationValue != null && initializationValue.getValue() != null) {
            if (initializationValue.getValue() instanceof String) {
                String value = (String) initializationValue.getValue();
                init = value;
            } else if (initializationValue.getValue() instanceof Integer) {
                Integer value = (Integer) initializationValue.getValue();
                init = allowedValues.get(value);
            }
        }

        EnumerateType et = new EnumerateType(getTypeName(), allowedValues, init);
        setBaseType(et);
        return et;
    }


    public void setInt(ScalarValue<? extends AnyInt, Long> val) {
        values.put(allowedValues.get(allowedValues.size() - 1), val);
        counter = (int) (val.getValue() + 1);
    }
}
