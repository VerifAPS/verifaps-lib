package edu.kit.iti.formal.automation.st.ast.operators;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.AnyBit;

class BooleanPromoter implements TypePromotion {
    public static final TypePromotion INSTANCE = new BooleanPromoter();

    @Override
    public Any getPromotion(Any a, Any b) {
        return AnyBit.BOOL;
    }
}