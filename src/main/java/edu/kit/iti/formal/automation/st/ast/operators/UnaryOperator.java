package edu.kit.iti.formal.automation.st.ast.operators;

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

    public boolean isValid(Any a) {
        return a.getClass().isAssignableFrom(validFor.getClass());
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
