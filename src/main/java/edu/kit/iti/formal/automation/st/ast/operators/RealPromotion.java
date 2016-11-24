package edu.kit.iti.formal.automation.st.ast.operators;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.AnyReal;

/**
 * Created by weigl on 24.11.16.
 */
public class RealPromotion implements TypePromotion {

    public static final TypePromotion INSTANCE = new RealPromotion();

    @Override
    public Any getPromotion(Any a, Any b) {
        try {
            return promote((AnyReal) a, (AnyReal) b);
        } catch (ClassCastException e) {
            return null;
        }
    }

    private Any promote(AnyReal a, AnyReal b) {
        if (a.equals(b)) return a;
        if (a instanceof AnyReal.LReal) {
            return a;
        } else {
            return b;
        }
    }
}