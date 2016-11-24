package edu.kit.iti.formal.automation.operators;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.AnyUInt;

public class UnaryOperator implements Operator {
    private final String symbol;
    private final Any validFor;

    public UnaryOperator(String symbol, Any any) {
        this.symbol = symbol;
        this.validFor = any;
        Operators.register(symbol, this);
    }

    @Override
    public String symbol() {
        return this.symbol;
    }

    @Override
    public Any[] getExpectedDataTypes() {
        return new Any[]{validFor};
    }

    public boolean isValid(Any a) {
        return validFor.getClass().isAssignableFrom(a.getClass());
    }

    public Any getPromotedType(Any a) {
        if (isValid(a)) {
            if (a instanceof AnyUInt) {
                AnyUInt anyUInt = (AnyUInt) a;
                return anyUInt.asSigned();
            }
            return a;
        }
        return null;
    }
}
